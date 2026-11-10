# -*- coding: utf-8 -*-
"""Global sensitivity analysis of CC-2: Morris screening (all parameters) and grouped Sobol' indices (Saltelli 2010
first-order and Jansen total-effect estimators) for the proposal as stated (R0) relative to the status quo.
Usage: python3 cc2_gsa.py [N_sobol] [r_morris]. Writes out/cc2_gsa.json."""
import os, sys, json, time
import numpy as np
from scipy.stats import qmc
from cc2_data import Geo
from cc2_params import NAMES, PRIORS, GROUPS, from_unit, DESIGNS
from cc2_model import draw_random, simulate, summarize
from cc2_chamber import chamber

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
N = int(sys.argv[1]) if len(sys.argv) > 1 else 1024
RM = int(sys.argv[2]) if len(sys.argv) > 2 else 10
DES = sys.argv[3] if len(sys.argv) > 3 else "R0"
geo = Geo()
OUTS = ["dval_need", "dval", "coop", "reg_share", "completion", "ch_leg_effort", "cond_top_t2", "persist_fail",
        "lose_mun", "sh_conflict_loss"]
ACTIVE = [g for g in GROUPS if g not in ("LRG", "Design")] if DES != "R15" else [g for g in GROUPS]


def take(R, rows):
    return {k: v[rows] for k, v in R.items()}


def evaluate(U, rows, R_base):
    """Model outputs for unit-cube points U (rows of R_base used for common random numbers)."""
    P = from_unit(U)
    out = {k: [] for k in OUTS}
    CH = 400
    for c0 in range(0, len(U), CH):
        sl = slice(c0, min(len(U), c0 + CH))
        Pc = {k: v[sl] for k, v in P.items()}
        Rc = take(R_base, rows[sl])
        sq = simulate(Pc, "SQ", geo, Rc)
        o = simulate(Pc, DES, geo, Rc)
        S = summarize(o, sq, geo, Pc)
        d = DESIGNS[DES]
        ch = chamber(Pc, geo.seats, o["cond_money_share"].mean(1), o["eta_eff"], d["closed_list"], d["abolish"])
        S["ch_leg_effort"] = ch["leg_effort"]
        S["cond_top_t2"] = o["cond_party_share"][:, 2, :].max(1)
        for k in OUTS:
            out[k].append(S[k])
    return {k: np.concatenate(v) for k, v in out.items()}


t0 = time.time()
res = {"design": DES, "N": N, "r_morris": RM, "groups": ACTIVE}
# ------------------------------------------------------------------ Morris (p = 4 levels at the midpoints of four equal
# intervals of each prior, 1/8, 3/8, 5/8, 7/8, and steps of two levels, delta = 1/2). Midpoint levels keep every
# evaluation inside the priors: the standard grid {0, 1/3, 2/3, 1} puts a quarter of the evaluations at complete
# relocation (eta = 1), where there is no county money and the county outcomes are zero by construction.
k = len(NAMES)
rng = np.random.default_rng(77)
levels = np.array([1 / 8, 3 / 8, 5 / 8, 7 / 8])
DELTA = 0.5
traj = [];
tid = []
for r in range(RM):
    x = rng.choice(levels[:2], size=k)                         # start so that +1/2 stays in [1/8, 7/8]
    pts = [x.copy()]
    for i in rng.permutation(k):
        x = x.copy();
        x[i] += DELTA
        pts.append(x)
    traj.append(np.array(pts));
    tid += [r] * (k + 1)
Um = np.vstack(traj)
Rm = draw_random(RM, geo, seed=909)
ym = evaluate(Um, np.array(tid), Rm)
mor = {}
for o in OUTS:
    ee = np.zeros((RM, k))
    for r in range(RM):
        pts = Um[r * (k + 1):(r + 1) * (k + 1)]
        y = ym[o][r * (k + 1):(r + 1) * (k + 1)]
        for s in range(k):
            i = int(np.argmax(np.abs(pts[s + 1] - pts[s])))
            ee[r, i] = (y[s + 1] - y[s]) / DELTA
    mor[o] = {"mu_star": dict(zip(NAMES, np.abs(ee).mean(0).round(5).tolist())),
              "sigma": dict(zip(NAMES, ee.std(0).round(5).tolist()))}
res["morris"] = mor
print(f"Morris done {time.time() - t0:.0f}s", flush=True)
# ------------------------------------------------------------------ grouped Sobol'
sob = qmc.Sobol(d=2 * k, scramble=True, seed=2027)
AB = sob.random_base2(int(np.log2(N)))
A, B = AB[:, :k], AB[:, k:]
gidx = {g: [i for i, n in enumerate(NAMES) if PRIORS[n][2] == g] for g in ACTIVE}
mats = [A, B] + [np.where(np.isin(np.arange(k), gidx[g])[None, :], B, A) for g in ACTIVE]
U_all = np.vstack(mats)
rows = np.tile(np.arange(N), len(mats))
Rs = draw_random(N, geo, seed=1313)
y = evaluate(U_all, rows, Rs)
print(f"Sobol runs done {time.time() - t0:.0f}s", flush=True)
sobol = {}
bs = np.random.default_rng(5)
for o in OUTS:
    Y = y[o].reshape(len(mats), N)
    fA, fB = Y[0], Y[1]
    ok = np.isfinite(Y).all(0)
    fA, fB, Y = fA[ok], fB[ok], Y[:, ok]
    V = np.var(np.concatenate([fA, fB]))
    S1, ST, S1ci, STci = {}, {}, {}, {}
    for gi, g in enumerate(ACTIVE):
        fAB = Y[2 + gi]
        s1 = np.mean(fB * (fAB - fA)) / V if V > 0 else 0.0
        st = 0.5 * np.mean((fA - fAB) ** 2) / V if V > 0 else 0.0
        boots1, bootst = [], []
        n_ = len(fA)
        for _ in range(200):
            ii = bs.integers(0, n_, n_)
            Vb = np.var(np.concatenate([fA[ii], fB[ii]]))
            if Vb > 0:
                boots1.append(np.mean(fB[ii] * (fAB[ii] - fA[ii])) / Vb)
                bootst.append(0.5 * np.mean((fA[ii] - fAB[ii]) ** 2) / Vb)
        S1[g], ST[g] = float(s1), float(st)
        S1ci[g] = [float(np.percentile(boots1, 2.5)), float(np.percentile(boots1, 97.5))]
        STci[g] = [float(np.percentile(bootst, 2.5)), float(np.percentile(bootst, 97.5))]
    sobol[o] = {"S1": S1, "ST": ST, "S1_ci": S1ci, "ST_ci": STci, "var": float(V), "n": int(ok.sum())}
res["sobol"] = sobol
res["seconds"] = time.time() - t0
json.dump(res, open(os.path.join(ROOT, "out", f"cc2_gsa_{DES}.json"), "w"), indent=1)
for o in OUTS:
    print(o, {g: (round(sobol[o]["S1"][g], 2), round(sobol[o]["ST"][g], 2)) for g in ACTIVE})
print(f"done {time.time() - t0:.0f}s")
