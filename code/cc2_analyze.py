# -*- coding: utf-8 -*-
"""Headline numbers, scenario discovery (Monte Carlo filtering and classification trees) and tables for CC-2.
Reads out/cc2_worlds.npz; writes out/cc2_numbers.json and out/cc2_discovery.json."""
import os, json
import numpy as np
from scipy.stats import ks_2samp
from sklearn.tree import DecisionTreeClassifier, export_text
from cc2_params import DESIGNS, NAMES, PRIORS, DESIGN_LABEL
from cc2_data import Geo, PARTIES

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
z = np.load(os.path.join(ROOT, "out", "cc2_worlds.npz"))
P = {k[2:]: z[k] for k in z.files if k.startswith("P|")}
W = len(P["s0"])


def g(d, k):
    return z[f"{d}|{k}"]


def q3(a):
    a = np.asarray(a, float)
    return [float(np.percentile(a, 50)), float(np.percentile(a, 5)), float(np.percentile(a, 95))]


num = {"W": W}
KEYS = ["need_top20_share", "dval", "dval_need", "reg_share", "completion", "coop", "coop_tl", "coop_el", "coop_opp", "coop_al",
        "coop_small", "effort", "effort_u", "fail", "fail_poor", "fail_rich", "persist_fail", "trap", "lose_mun",
        "lose_pop", "gini", "corr_need", "approval_bind", "conde_turnover", "sel_competence", "tilt",
        "sh_conflict_loss", "sh_scale_gain", "sh_quality_gain", "sh_cofin_paid", "sh_reg_value", "sh_salvage",
        "sh_abandoned_cost", "sh_unfinished_end", "sh_admin", "sh_lrg_cost", "sh_div_mun", "sh_div_cty", "sh_div_sq",
        "div_total", "ch_leg_effort", "ch_leg_output", "ch_leg_skill", "ch_leg_skill_sq", "ch_leg_output_sel_only",
        "ch_leg_output_eff_only", "ch_brok_skill", "cond_PL_t0", "cond_PL_t1", "cond_PL_t2", "cond_top_t0",
        "cond_top_t1", "cond_top_t2", "cond_hhi_t0", "cond_hhi_t2", "money_PL", "persist_all3", "switch_t1",
        "mayor_PL_2032", "mayor_PL_2036", "eta_eff"] + [f"dval_size_{c}" for c in
                                                         ("<5k", "5-10k", "10-20k", "20-50k", "50-100k", ">100k")]
for d in DESIGNS:
    num[d] = {}
    for k in KEYS:
        if f"{d}|{k}" in z.files:
            num[d][k] = q3(g(d, k))
    for p in ("PL", "MDB", "PT", "PSD", "UNIÃO", "NOVO", "CIDADANIA"):
        for k in ("X", "psi", "eL_party"):
            if f"{d}|{k}_{p}" in z.files:
                num[d][f"{k}_{p}"] = q3(g(d, f"{k}_{p}"))
    if d != "SQ":
        num[d]["P_dval_pos"] = float((g(d, "dval") > 0).mean())
        num[d]["P_dval_need_pos"] = float((g(d, "dval_need") > 0).mean())
        num[d]["P_beats_R0_need"] = float((g(d, "dval_need") > g("R0", "dval_need")).mean())
        num[d]["P_beats_R0_real"] = float((g(d, "dval") > g("R0", "dval")).mean())
        num[d]["P_leg_effort_up"] = float((g(d, "ch_leg_effort") > 1 - P["s0"]).mean())
        num[d]["P_all_parties_gain"] = float(g(d, "ch_all_parties_gain").mean())
# decomposition of the proposal: reallocation (D0 vs SQ), county institutions (R0 vs D0)
num["decomp"] = {
    "realloc_real": q3(g("D0", "dval")), "realloc_need": q3(g("D0", "dval_need")),
    "institutions_real": q3(g("R0", "dval") - g("D0", "dval")),
    "institutions_need": q3(g("R0", "dval_need") - g("D0", "dval_need")),
    "P_institutions_real_pos": float((g("R0", "dval") > g("D0", "dval")).mean()),
    "P_institutions_need_pos": float((g("R0", "dval_need") > g("D0", "dval_need")).mean()),
    "law_on_SQ_vs_law_on_R0_need": float((g("L0", "dval_need") > g("R14", "dval_need")).mean()),
    "law_on_SQ_vs_law_on_R0_real": float((g("L0", "dval") > g("R14", "dval")).mean()),
}
# effect of single design changes relative to R0 (paired)
pairs = {}
for d in DESIGNS:
    if d in ("SQ", "CL", "L0", "R0"):
        continue
    for k in ("dval", "dval_need", "coop", "completion", "reg_share", "persist_fail", "conde_turnover",
              "sh_conflict_loss", "effort"):
        if f"{d}|{k}" in z.files:
            diff = g(d, k) - g("R0", k)
            tol = 1e-9 * (1 + np.abs(g("R0", k)))
            pairs.setdefault(d, {})[k] = q3(diff) + [float((diff > tol).mean())]
num["pairs_vs_R0"] = pairs
# mechanism slices: cooperation and value by key parameters (terciles)
sl = {}
for k in ("eta_X", "sig_bar", "nu", "eps_x", "zeta_opp", "q_loc0", "c_host", "ell", "s_bar", "beta_bw", "V_R",
          "rho_R", "kap_party", "g_pool", "zeta"):
    qq = np.quantile(P[k], [1 / 3, 2 / 3])
    b = np.digitize(P[k], qq)
    sl[k] = {o: [float(np.median(g("R0", o)[b == i])) for i in range(3)] for o in
             ("dval", "dval_need", "coop", "reg_share", "completion", "cond_top_t2", "persist_fail")}
num["slices_R0"] = sl
json.dump(num, open(os.path.join(ROOT, "out", "cc2_numbers.json"), "w"), indent=1)

# ------------------------------------------------------------------ scenario discovery
X = np.column_stack([P[n] for n in NAMES])
disc = {}


def discover(name, y, feats=None, depth=3):
    feats = feats or NAMES
    Xf = np.column_stack([P[n] for n in feats])
    ks = {n: float(ks_2samp(P[n][y], P[n][~y]).statistic) for n in feats} if 0 < y.mean() < 1 else {}
    top = sorted(ks.items(), key=lambda t: -t[1])[:8]
    clf = DecisionTreeClassifier(max_depth=depth, min_samples_leaf=60, random_state=0).fit(Xf, y)
    acc = float(clf.score(Xf, y))
    base = float(max(y.mean(), 1 - y.mean()))
    disc[name] = {"rate": float(y.mean()), "ks_top": top, "tree_acc": acc, "base_acc": base,
                  "tree": export_text(clf, feature_names=list(feats), decimals=3)}


active = [n for n in NAMES if PRIORS[n][2] not in ("LRG", "Design")]
discover("R0_beats_SQ_need", g("R0", "dval_need") > 0, active)
discover("R0_beats_SQ_real", g("R0", "dval") > 0, active)
discover("R0_institutions_add_value", g("R0", "dval") > g("D0", "dval"), active)
discover("R0_coop_high", g("R0", "coop") >= 0.75, active)
discover("R0_reg_share_high", g("R0", "reg_share") >= 0.2, active)
discover("R0_all_parties_more_legislation", g("R0", "ch_all_parties_gain") > 0.5,
         ["s0", "pi", "kappa", "eta_X", "chi_c", "phi_P", "beta_bw", "c_dir", "h_sw"])
discover("bar_helps_value", g("R0", "dval") > g("R2", "dval"), active)
# high cooperation and the effect of the bar on completion (Supplementary Material 06, Section S6.2)
discover("R0_coop_ge_0.8", g("R0", "coop") >= 0.8, active)
discover("bar_raises_completion", g("R0", "completion") > g("R2", "completion"), active)
discover("R15_beats_SQ_need", g("R15", "dval_need") > 0)
json.dump(disc, open(os.path.join(ROOT, "out", "cc2_discovery.json"), "w"), indent=1)
for k, v in disc.items():
    print("==", k, "rate", round(v["rate"], 3), "tree acc", round(v["tree_acc"], 3), "base", round(v["base_acc"], 3))
    print("   KS:", [(a, round(b, 2)) for a, b in v["ks_top"][:6]])
    print(v["tree"])
