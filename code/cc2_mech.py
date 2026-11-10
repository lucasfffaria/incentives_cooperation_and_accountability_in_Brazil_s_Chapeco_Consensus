# -*- coding: utf-8 -*-
"""Instrumented runs of CC-2 that record mechanism-level data for the figures: participants' cooperation
(Proposition 4), projects' completion and choice (Proposition 3), counties' scores and failures by capacity.
Writes out/cc2_mech.npz."""
import os
import numpy as np
from scipy.special import expit
import cc2_model as cm
from cc2_data import Geo
from cc2_params import sample, CONST

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
geo = Geo()
W = 300
P, _ = sample(W, seed=99)
R = cm.draw_random(W, geo, seed=77)
rec = {"coop": [], "proj": [], "cty": []}
state = {"design": None, "tau": None}
orig_plan, orig_real = cm.make_plan, cm.realize


def plan_hook(j, tau, geo_, P_, Pc, R_, d, chi, party, tl, cparty, ctheta, ccomp, ptenure, inc_run, Bn, v1, qm, gam,
              kap_cred, insp, ta, O, **kw):
    out = orig_plan(j, tau, geo_, P_, Pc, R_, d, chi, party, tl, cparty, ctheta, ccomp, ptenure, inc_run, Bn, v1, qm,
                    gam, kap_cred, insp, ta, O, **kw)
    idx = geo_.members[j]
    C, V, qx, sel = out["C"], out["V"], out["qx_menu"], out["sel"]
    sig = V / np.maximum(C, 1e-9) - 1
    k = np.arange(C.shape[1])
    for wi in range(0, W, 3):                                  # thin the sample
        for kk in k:
            rec["proj"].append((state["design"], tau, j, wi, sig[wi, kk], qx[wi, kk], float(sel[wi, kk]),
                                ctheta[wi, j], C[wi, kk] / max(Bn[wi, j], 1)))
    out["_tau"] = tau
    return out


def real_hook(j, tau, geo_, P_, Pc, R_, d, chi, pl, e_star, party, cparty, ctheta, inc_run, Bn, x_sq, reloc, can_re,
              O, insp, u_star):
    res = orig_real(j, tau, geo_, P_, Pc, R_, d, chi, pl, e_star, party, cparty, ctheta, inc_run, Bn, x_sq, reloc,
                    can_re, O, insp, u_star)
    idx = geo_.members[j]
    sel, part, stake, w, V = pl["sel"], pl["part"], pl["stake"], pl["w"], pl["V"]
    # recompute the equilibrium at the chosen effort to record each participant's terms
    Q = np.clip(pl["Q0"] * (1 + P_["alpha_e"] * e_star), 0, 1)[:, None] * np.ones((1, V.shape[1]))
    gt = pl["gt"]
    F_m = (gt[:, None, :] * w * V[..., None] * Q[..., None] * sel[..., None]).sum(1)
    dF = pl["beta4"][:, None] * pl["pstay"] * pl["pcont"][:, None] * F_m
    p, qx, A, Hk, Fk = cm.coop_equilibrium(Q, V, pl["C"], w, pl["wt"], part & sel[..., None],
                                           pl["hostm"] & sel[..., None], stake * sel[..., None], gt, dF, Pc, chi)
    ps = part & sel[..., None]
    wsel = np.where(ps)
    take = np.arange(len(wsel[0]))[::7]
    for t in take:
        wi, kk, mi = wsel[0][t], wsel[1][t], wsel[2][t]
        st = stake[wi, kk, mi]
        rec["coop"].append((state["design"], tau, j, wi, p[wi, kk, mi], dF[wi, mi] / max(st, 1e-9),
                            gt[wi, mi] * w[wi, kk, mi] * V[wi, kk] * qx[wi, kk] * Pc["eps_x"][wi] / max(st, 1e-9),
                            float(pl["pstay"][wi, mi] == 0), float(pl["opp"][wi, mi]),
                            float(geo_.pop[idx[mi]] < 10000), float(pl["hostm"][wi, kk, mi]), pl["pcont"][wi],
                            w[wi, kk, mi], pl["wt"][wi, kk, mi]))
    rec["cty"].append((state["design"], tau, j, res["Dreal"].copy(), e_star.copy(), u_star.copy()))
    return res


cm.make_plan, cm.realize = plan_hook, real_hook
for dsg in ("R0", "R1", "R2", "R3", "R8", "R12"):
    state["design"] = dsg
    cm.simulate(P, dsg, geo, R)
cm.make_plan, cm.realize = orig_plan, orig_real
dt_c = np.dtype([("design", "U4"), ("tau", "i1"), ("j", "i1"), ("w", "i2"), ("p", "f4"), ("fut", "f4"), ("excl", "f4"),
                 ("tl", "f4"), ("opp", "f4"), ("small", "f4"), ("host", "f4"), ("pcont", "f4"), ("wshare", "f4"),
                 ("cshare", "f4")])
dt_p = np.dtype([("design", "U4"), ("tau", "i1"), ("j", "i1"), ("w", "i2"), ("sig", "f4"), ("q", "f4"), ("sel", "f4"),
                 ("theta", "f4"), ("size", "f4")])
coop = np.array(rec["coop"], dtype=dt_c)
proj = np.array(rec["proj"], dtype=dt_p)
np.savez_compressed(os.path.join(ROOT, "out", "cc2_mech.npz"), coop=coop, proj=proj,
                    P_zeta=P["zeta"], P_eps=P["eps_x"])
print(len(coop), len(proj))
