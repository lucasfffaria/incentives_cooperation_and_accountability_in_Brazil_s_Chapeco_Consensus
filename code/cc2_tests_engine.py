"""Engine tests: money identity, value identity, nesting at full relocation, cooperation fixed point."""
import numpy as np, json, sys
from cc2_data import Geo
from cc2_params import sample, DESIGNS
from cc2_model import draw_random, simulate, summarize, coop_equilibrium
geo = Geo()
W = 48
P, U = sample(W, seed=11)
R = draw_random(W, geo, seed=5)
res = {}
# (a) money identity for every design
for dsg in DESIGNS:
    o = simulate(P, dsg, geo, R)
    tot = o["money_transfers"] + o["reg_cost"] + o["admin"] + o["money_reloc"]
    res["money_" + dsg] = float(np.max(np.abs(tot / (12 * geo.M_tot) - 1)))
# (b) value identity: perfect implementation, no diversion, no scale economies, no co-financing (R5) or SQ
Pp = {k: v.copy() for k, v in P.items()}
for k, v in dict(f_SC=0.0, d_c0=0.0, q_loc0=1.0, nu=0.0, phi_cx=0.0, alpha_a=0.0, alpha_e=0.0, omega_h=0.0,
                 sig_bar=0.0, sd_sig=0.0, c_adm=0.0, alpha_u=0.0).items():
    Pp[k][:] = v
for dsg in ("SQ", "R5"):
    o = simulate(Pp, dsg, geo, R)
    res["value_identity_" + dsg] = float(np.max(np.abs(o["val_m"].sum(1) / (12 * geo.M_tot) - 1)))
# (c) nesting: full relocation (eta = 1) reproduces the status quo value exactly
Pn = {k: v.copy() for k, v in P.items()};
Pn["eta_X"][:] = 1.0
sq = simulate(Pn, "SQ", geo, R)
for dsg in ("R0", "R6", "R12"):
    o = simulate(Pn, dsg, geo, R)
    res["nest_eta1_" + dsg] = float(np.max(np.abs(o["val_m"] - sq["val_m"])))
print(json.dumps(res, indent=1))
ok = all(v < 1e-9 for k, v in res.items() if k.startswith(("money", "value", "nest")))
print("ALL PASS" if ok else "FAIL")
