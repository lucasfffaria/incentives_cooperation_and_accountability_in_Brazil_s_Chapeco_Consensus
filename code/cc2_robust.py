# -*- coding: utf-8 -*-
"""Robustness runs of CC-2 (1,000 worlds each): status-quo allocation variants, macro-regions as counties,
party-line college voting, strong bandwagon with costless tilting, no capacity gradient, and targets set on outcome
indicators. Writes out/cc2_robust.json."""
import os, json, time
import numpy as np
from cc2_data import Geo
from cc2_params import sample
from cc2_model import draw_random, simulate, summarize
from cc2_chamber import chamber
from cc2_params import DESIGNS

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
N = 1000
P0, _ = sample(N, seed=20261008)
out = {}
t0 = time.time()


def run(tag, geo, P, designs=("D0", "R0", "R15"), pairs=()):
    R = draw_random(N, geo, seed=4242)
    sq = simulate(P, "SQ", geo, R)
    res = {}
    keep = {}
    for dsg in designs:
        o = simulate(P, dsg, geo, R)
        S = summarize(o, sq, geo, P)
        d = DESIGNS[dsg]
        ch = chamber(P, geo.seats, o["cond_money_share"].mean(1), o["eta_eff"], d["closed_list"], d["abolish"])
        S["ch_leg_effort"] = ch["leg_effort"]
        cs = o["cond_party_share"]
        S["cond_PL_t0"], S["cond_PL_t2"] = cs[:, 0, 0], cs[:, 2, 0]
        S["cond_top_t2"] = cs[:, 2, :].max(1)
        ch_ = o["cparty_hist"]
        S["persist_all3"] = ((ch_[:, 0] == ch_[:, 1]) & (ch_[:, 1] == ch_[:, 2]) & (ch_[:, 0] >= 0)).mean(1)
        res[dsg] = {k: [float(np.median(v)), float(np.percentile(v, 5)), float(np.percentile(v, 95)),
                        float((v > 0).mean()), float(np.mean(v))] for k, v in S.items() if np.ndim(v) == 1}
        keep[dsg] = S
    # paired comparisons (share of worlds in which the first design is above / below the second)
    for a, b in pairs:
        for k in ("effort", "effort_u", "coop", "completion", "dval", "dval_need", "fail_poor", "persist_fail"):
            x, y = keep[a][k], keep[b][k]
            tol = 1e-9 * (1 + np.abs(y))
            res[f"{a}_vs_{b}|{k}"] = [float((x > y + tol).mean()), float((x < y - tol).mean()), float(np.median(x - y))]
    out[tag] = res
    print(tag, f"{time.time() - t0:.0f}s", {d: (round(res[d]["dval"][0], 2), round(res[d]["dval_need"][0], 2))
                                          for d in designs}, flush=True)


run("main_1000", Geo(), P0)
run("sq_pooled", Geo(sq_variant="pooled"), P0)
run("sq_health_half", Geo(sq_variant="health"), P0)
run("sq_pooled_low", Geo(sq_variant="pooled_low"), P0)
run("sq_chamber2026", Geo(sq_variant="chamber2026"), P0)
run("macro_regions", Geo(counties="macro"), P0)
Pp = {k: v.copy() for k, v in P0.items()};
Pp["phi_P"][:] = 8.0
run("party_line_college", Geo(), Pp)
Pb = {k: v.copy() for k, v in P0.items()};
Pb["beta_bw"] = 0.3 + 0.3 * (Pb["beta_bw"] / 0.3);
Pb["c_T"][:] = 0.0
run("strong_bandwagon_free_tilt", Geo(), Pb, designs=("R0", "R6"))
Pn = {k: v.copy() for k, v in P0.items()};
Pn["nu"][:] = 0.0
run("no_capacity_gradient", Geo(), Pn)
# targets on the outcome indicators of the managerial law: the companion paper finds that the component of municipal
# indicators that changes with the administration is 0-3.3% of their within-state variance and that noise is large
# in small municipalities; county aggregates are larger, so the noise share is set lower than for small municipalities
Po = {k: v.copy() for k, v in P0.items()}
Po["w_perf"] = 0.003 + 0.030 * (P0["w_cap"] - 0.3) / 0.3          # U[0.003, 0.033], same unit-cube draws
Po["w_noise"] = 0.02 + 0.18 * (P0["w_noise"] - 0.2) / 0.3         # U[0.02, 0.20]
run("outcome_targets", Geo(), Po, designs=("R0", "R2", "R8"), pairs=(("R0", "R2"), ("R0", "R8")))
run("main_targets_pairs", Geo(), P0, designs=("R0", "R2", "R8"), pairs=(("R0", "R2"), ("R0", "R8")))
json.dump(out, open(os.path.join(ROOT, "out", "cc2_robust.json"), "w"), indent=1)
print("done", round(time.time() - t0))
