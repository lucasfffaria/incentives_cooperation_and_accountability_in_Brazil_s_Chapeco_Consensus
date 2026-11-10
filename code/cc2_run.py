# -*- coding: utf-8 -*-
"""Main experiment of CC-2: N worlds x all designs, common random numbers, same money.
Writes out/cc2_worlds.npz (parameters and per-world outputs), out/cc2_mun.npz (per-municipality values for selected
designs) and out/cc2_run.log."""
import os, sys, time, json
import numpy as np
from cc2_data import Geo, PARTIES
from cc2_params import sample, DESIGNS, NAMES
from cc2_model import draw_random, simulate, summarize, T_TERMS
from cc2_chamber import chamber

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, "out")
os.makedirs(OUT, exist_ok=True)
N = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
CHUNK = 500
SEED_P, SEED_R = 20261008, 4242
KEEP_MUN = ("SQ", "D0", "R0", "R3", "R10", "R12", "R15", "R16", "L0", "R14")
geo = Geo()
P_all, U_all = sample(N, seed=SEED_P)
res = {d: {} for d in DESIGNS}
mun = {d: [] for d in KEEP_MUN}
t0 = time.time()
for c0 in range(0, N, CHUNK):
    sl = slice(c0, min(N, c0 + CHUNK))
    P = {k: v[sl] for k, v in P_all.items()}
    W = sl.stop - sl.start
    R = draw_random(W, geo, seed=SEED_R + c0)
    sq = simulate(P, "SQ", geo, R)
    for dsg, d in DESIGNS.items():
        o = sq if dsg == "SQ" else simulate(P, dsg, geo, R)
        S = summarize(o, sq, geo, P)
        s_cond = o["cond_money_share"].mean(1)
        ch = chamber(P, geo.seats, s_cond, o["eta_eff"], d["closed_list"], d["abolish"])
        for k, v in ch.items():
            if k in ("X", "psi", "eL_party"):
                for p in np.where(geo.seats > 0)[0]:
                    S[f"{k}_{PARTIES[p]}"] = v[:, p]
            else:
                S["ch_" + k] = v
        # partisan control
        cs = o["cond_party_share"]
        for t in range(T_TERMS):
            S[f"cond_PL_t{t}"] = cs[:, t, 0]
            S[f"cond_top_t{t}"] = cs[:, t, :].max(1)
            S[f"cond_hhi_t{t}"] = (cs[:, t, :] ** 2).sum(1)
        ms = o["cond_money_share"]
        S["money_PL"] = ms[:, :, 0].mean(1)
        ch_ = o["cparty_hist"]
        S["persist_all3"] = ((ch_[:, 0] == ch_[:, 1]) & (ch_[:, 1] == ch_[:, 2]) & (ch_[:, 0] >= 0)).mean(1)
        S["switch_t1"] = ((ch_[:, 0] != ch_[:, 1]) & (ch_[:, 0] >= 0)).mean(1)
        ms_ = o["mayor_share"]
        S["mayor_PL_2032"] = ms_[:, 2, 0];
        S["mayor_PL_2036"] = ms_[:, 3, 0]
        # mayors of the conde's party in the county, last college vs first
        for k, v in S.items():
            res[dsg].setdefault(k, []).append(np.asarray(v, dtype=float))
        if dsg in KEEP_MUN:
            mun[dsg].append(o["val_m"].astype(np.float32))
    print(f"chunk {c0}-{sl.stop}: {time.time() - t0:.0f}s", flush=True)
flat = {}
for dsg in DESIGNS:
    for k, v in res[dsg].items():
        flat[f"{dsg}|{k}"] = np.concatenate(v)
np.savez_compressed(os.path.join(OUT, "cc2_worlds.npz"), U=U_all, names=np.array(NAMES), **flat,
                    **{"P|" + k: v for k, v in P_all.items()})
np.savez_compressed(os.path.join(OUT, "cc2_mun.npz"), **{d: np.concatenate(v) for d, v in mun.items()})
print(f"done: {N} worlds, {len(DESIGNS)} designs, {time.time() - t0:.0f}s")
