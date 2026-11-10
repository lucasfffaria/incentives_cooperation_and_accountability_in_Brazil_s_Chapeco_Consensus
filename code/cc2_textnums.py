# -*- coding: utf-8 -*-
"""Conditional and derived numbers quoted in the text (Sections 1 and 6), computed from out/cc2_worlds.npz.
Writes out/cc2_text_numbers.json. Every number in the Results section that is not in a table comes from here."""
import os, json
import numpy as np

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
z = np.load(os.path.join(ROOT, "out", "cc2_worlds.npz"))
P = {k[2:]: z[k] for k in z.files if k.startswith("P|")}
g = lambda d, k: z[f"{d}|{k}"]
med = lambda a: float(np.median(a))
mean = lambda a: float(np.mean(a))
sh = lambda b: float(np.mean(b))
T = {}
# ------------------------------------------------------------------ 6.1 Chamber
e0 = 1 - P["s0"]
T["effort_sq_med"] = med(e0)
for d in ("R0", "CL", "R13", "D0"):
    T[f"effort_{d}_med"] = med(g(d, "ch_leg_effort"))
    T[f"effort_{d}_P_up"] = sh(g(d, "ch_leg_effort") > e0)
eta = P["eta_X"]
for lo, hi in ((0, .25), (.25, .5), (.5, .75), (.75, 1.01)):
    s = (eta >= lo) & (eta < hi)
    T[f"effort_R0_eta_{lo}_{hi}"] = med(g("R0", "ch_leg_effort")[s])
    T[f"effort_CL_eta_{lo}_{hi}"] = med(g("CL", "ch_leg_effort")[s])
    T[f"effort_R0_P_up_eta_{lo}_{hi}"] = sh(g("R0", "ch_leg_effort")[s] > e0[s])
T["effort_R0_eta_ge_.5"] = med(g("R0", "ch_leg_effort")[eta >= .5])
T["effort_R0_eta_lt_.5"] = med(g("R0", "ch_leg_effort")[eta < .5])
T["R0_minus_CL_eta_ge_.9"] = med((g("R0", "ch_leg_effort") - g("CL", "ch_leg_effort"))[eta >= .9])
T["R0_minus_CL_all"] = med(g("R0", "ch_leg_effort") - g("CL", "ch_leg_effort"))
# PL versus other parties (effort = 1 - eB)
pl = g("R0", "eL_party_PL")
from cc2_data import SEATS as SEATS_ALL
SEATS = {p: s for p, s in SEATS_ALL.items() if p != "PL"}   # seat-weighted, as in Figure 3c
oth = sum(g("R0", f"eL_party_{p}") * s for p, s in SEATS.items()) / sum(SEATS.values())
T["effort_others_minus_PL_med"] = med(oth - pl)
T["effort_others_minus_PL_eta_lt_.25"] = med((oth - pl)[eta < .25])
T["effort_others_minus_PL_eta_ge_.75"] = med((oth - pl)[eta >= .75])
T["P_all_parties_gain"] = sh(g("R0", "ch_all_parties_gain"))
T["psi_PL_med"] = med(g("R0", "psi_PL"))
T["psi_MDB_med"] = med(g("R0", "psi_MDB"))
T["X_PL_med"] = med(g("R0", "X_PL"))
# selection
sk_sq, sk_r0 = g("SQ", "ch_leg_skill"), g("R0", "ch_leg_skill")
T["skill_sq_med"], T["skill_R0_med"] = med(sk_sq), med(sk_r0)
T["skill_P_up"] = sh(sk_r0 > sk_sq)
if "sig_nu" in P and "sig_eps" in P:
    lessnoisy = P["sig_nu"] < P["sig_eps"]
    T["skill_P_up_listmakers_less_noisy"] = sh((sk_r0 > sk_sq)[lessnoisy])
    T["skill_P_up_listmakers_noisier"] = sh((sk_r0 > sk_sq)[~lessnoisy])
    T["share_worlds_listmakers_less_noisy"] = sh(lessnoisy)
T["brok_skill_sq_med"] = med(g("SQ", "ch_brok_skill"))
T["brok_skill_R0_med"] = med(g("R0", "ch_brok_skill"))
T["leg_output_R0_med"] = med(g("R0", "ch_leg_output"))
T["leg_output_R0_sel_only_med"] = med(g("R0", "ch_leg_output_sel_only"))
T["leg_output_R0_eff_only_med"] = med(g("R0", "ch_leg_output_eff_only"))
T["leg_output_CL_med"] = med(g("CL", "ch_leg_output"))
# ------------------------------------------------------------------ 6.2 control and persistence
for t in range(3):
    T[f"cond_PL_t{t}_mean"] = mean(g("R0", f"cond_PL_t{t}"))
    T[f"cond_top_t{t}_mean"] = mean(g("R0", f"cond_top_t{t}"))
    T[f"cond_top_t{t}_med"] = med(g("R0", f"cond_top_t{t}"))
T["cond_PL_t0_P_majority"] = sh(g("R0", "cond_PL_t0") > 0.5)
T["cond_top_t2_P_majority"] = sh(g("R0", "cond_top_t2") > 0.5)
T["money_PL_mean"] = mean(g("R0", "money_PL"))
T["persist_all3_mean"] = mean(g("R0", "persist_all3"))
bw = P["beta_bw"]
qb = np.quantile(bw, [1 / 3, 2 / 3])
T["persist_all3_bw_low"] = mean(g("R0", "persist_all3")[bw < qb[0]])
T["persist_all3_bw_high"] = mean(g("R0", "persist_all3")[bw >= qb[1]])
T["persist_all3_R6_mean"] = mean(g("R6", "persist_all3"))
T["persist_all3_R1_mean"] = mean(g("R1", "persist_all3"))
T["persist_all3_R12_mean"] = mean(g("R12", "persist_all3")) if "R12|persist_all3" in z.files else None
T["cond_top_t2_bw_low"] = mean(g("R0", "cond_top_t2")[bw < qb[0]])
T["cond_top_t2_bw_high"] = mean(g("R0", "cond_top_t2")[bw >= qb[1]])
T["mayor_PL_2032_mean"] = mean(g("R0", "mayor_PL_2032"))
T["mayor_PL_2036_mean"] = mean(g("R0", "mayor_PL_2036"))
T["mayor_PL_2032_SQ_mean"] = mean(g("SQ", "mayor_PL_2032"))
T["mayor_PL_2036_SQ_mean"] = mean(g("SQ", "mayor_PL_2036"))
T["switch_t1_R0_mean"] = mean(g("R0", "switch_t1"))
T["conde_turnover_R0_mean"] = mean(g("R0", "conde_turnover"))
T["conde_turnover_R2_mean"] = mean(g("R2", "conde_turnover"))
T["sel_competence_R0_mean"] = mean(g("R0", "sel_competence"))
T["sel_competence_R2_mean"] = mean(g("R2", "sel_competence"))
T["tilt_R0_mean_Rm_per_term"] = mean(g("R0", "tilt")) / 1e6 / 3
T["tilt_R0_share_of_county_money"] = mean(g("R0", "tilt") / (12 * 595.2e6 * (1 - P["eta_X"])))
# ------------------------------------------------------------------ 6.3 distribution
for d in ("SQ", "D0", "R0", "R10", "R16"):
    T[f"gini_{d}_med"] = med(g(d, "gini"))
    T[f"need_top20_{d}_med"] = med(g(d, "need_top20_share"))
for d in ("D0", "R0", "R16"):
    T[f"lose_mun_{d}_med"] = med(g(d, "lose_mun"))
    T[f"lose_pop_{d}_med"] = med(g(d, "lose_pop"))
    for c in ("<5k", "5-10k", "10-20k", "20-50k", "50-100k", ">100k"):
        T[f"dval_size_{c}_{d}_med"] = med(g(d, f"dval_size_{c}"))
T["gini_D0_eta_lt_.25"] = med(g("D0", "gini")[eta < .25])
T["gini_D0_eta_ge_.75"] = med(g("D0", "gini")[eta >= .75])
T["gini_R0_eta_lt_.25"] = med(g("R0", "gini")[eta < .25])
T["gini_R0_eta_ge_.75"] = med(g("R0", "gini")[eta >= .75])
# mean and median contribution of the county institutions (R0 - D0), to reconcile with the mean decomposition
T["institutions_real_mean"] = mean(g("R0", "dval") - g("D0", "dval"))
T["dval_R0_mean"] = mean(g("R0", "dval"))
# ------------------------------------------------------------------ 6.4 value
for d in ("D0", "R0", "R1", "R2", "R3", "R4", "R5", "R12", "R13", "R14", "R15", "R16", "L0", "R10"):
    T[f"dval_{d}_med"] = med(g(d, "dval"))
    T[f"dval_need_{d}_med"] = med(g(d, "dval_need"))
    T[f"dval_{d}_P_pos"] = sh(g(d, "dval") > 0)
    T[f"dval_need_{d}_P_pos"] = sh(g(d, "dval_need") > 0)
    T[f"div_total_{d}_med"] = med(g(d, "div_total")) / 1e6
T["div_total_SQ_med"] = med(g("SQ", "div_total")) / 1e6
inst = g("R0", "dval") - g("D0", "dval")
T["institutions_real_med"] = med(inst)
T["institutions_real_P_pos"] = sh(inst > 0)
T["institutions_real_p5"], T["institutions_real_p95"] = float(np.percentile(inst, 5)), float(np.percentile(inst, 95))
sb, pc = P["sig_bar"], P["phi_cx"]
DISC = json.load(open(os.path.join(ROOT, "out", "cc2_discovery.json")))


def thr(tree, var, value):
    """Return a threshold used in the text after checking that the classification tree splits there."""
    assert f"{var} <= {value:.3f}" in DISC[tree]["tree"], (tree, var, value)
    return value


SB_I, PC_I = thr("R0_institutions_add_value", "sig_bar", 0.092), thr("R0_institutions_add_value", "phi_cx", 0.177)
good = (sb > SB_I) & (pc <= PC_I)              # main positive branch of the classification tree
T["institutions_box"] = {"sig_bar_gt": SB_I, "phi_cx_le": PC_I}
T["share_worlds_institutions_box"] = sh(good)
T["institutions_P_pos_in_good_box"] = sh((inst > 0)[good])
T["institutions_P_pos_outside_box"] = sh((inst > 0)[~good])
T["institutions_med_in_good_box"] = med(inst[good])
NU_R = thr("R0_beats_SQ_real", "nu", 0.137)
T["nu_split"] = NU_R
T["dval_R0_P_pos_nu_low"] = sh((g("R0", "dval") > 0)[P["nu"] <= NU_R])
T["dval_R0_P_pos_nu_high"] = sh((g("R0", "dval") > 0)[P["nu"] > NU_R])
T["dval_D0_P_pos_nu_lt_.05"] = sh((g("D0", "dval") > 0)[P["nu"] < 0.05])
zeta = P["zeta"]
ZE_N, SB_N, Q_N = (thr("R0_beats_SQ_need", "zeta", 0.308), thr("R0_beats_SQ_need", "sig_bar", 0.080),
                   thr("R0_beats_SQ_need", "q_loc0", 0.679))
ql = P["q_loc0"]
bx = (zeta <= ZE_N) & (sb > SB_N) & (ql > Q_N)       # positive leaf of the tree
T["need_box"] = {"zeta_le": ZE_N, "sig_bar_gt": SB_N, "q_loc0_gt": Q_N}
T["dval_need_R0_P_pos_box"] = sh((g("R0", "dval_need") > 0)[bx])
T["share_worlds_need_box"] = sh(bx)
T["dval_need_R0_P_pos_box_q_low"] = sh((g("R0", "dval_need") > 0)[(zeta <= ZE_N) & (sb > SB_N) & (ql <= Q_N)])
T["dval_need_R0_P_pos_zeta_low_sig_low"] = sh((g("R0", "dval_need") > 0)[(zeta <= ZE_N) & (sb <= SB_N)])
T["dval_need_R0_P_pos_zeta_high"] = sh((g("R0", "dval_need") > 0)[zeta > ZE_N])
T["share_worlds_zeta_low_sig_high"] = sh((zeta <= ZE_N) & (sb > SB_N))
T["dval_need_R0_P_pos_zeta_low_sig_high"] = sh((g("R0", "dval_need") > 0)[(zeta <= ZE_N) & (sb > SB_N)])
T["dval_need_R15_P_pos_zeta_lt_.5"] = sh((g("R15", "dval_need") > 0)[zeta < .5])
T["dval_need_R15_P_pos_zeta_ge_.5"] = sh((g("R15", "dval_need") > 0)[zeta >= .5])
T["dval_need_R16_P_pos_zeta_lt_.5"] = sh((g("R16", "dval_need") > 0)[zeta < .5])
T["dval_need_R16_P_pos_zeta_ge_.5"] = sh((g("R16", "dval_need") > 0)[zeta >= .5])
for d in ("R0", "R3", "R5", "R12", "R15", "R14", "R1", "R4"):
    T[f"reg_share_{d}_med"] = med(g(d, "reg_share"))
    T[f"completion_{d}_med"] = med(g(d, "completion"))
    T[f"coop_{d}_med"] = med(g(d, "coop"))
for k in ("sh_conflict_loss", "sh_scale_gain", "sh_quality_gain", "sh_abandoned_cost", "sh_unfinished_end",
          "sh_admin", "sh_cofin_paid", "sh_reg_value", "sh_salvage", "sh_lrg_cost"):
    for d in ("R0", "R3", "R5", "R15"):
        if f"{d}|{k}" in z.files:
            T[f"{k}_{d}_mean"] = mean(g(d, k))
# ------------------------------------------------------------------ 6.5 cooperation
for d in ("R0", "R1", "R3", "R4", "R12", "R15", "R2"):
    for k in ("coop_tl", "coop_el", "coop_opp", "coop_al", "coop_small"):
        if f"{d}|{k}" in z.files:
            T[f"{k}_{d}_med"] = med(g(d, k))
ex, ell = P["eps_x"], P["ell"]
b75 = ((ex > thr("R0_coop_high", "eps_x", 0.307)) & (ell <= thr("R0_coop_high", "ell", 0.207))
       & (P["phi_cx"] <= thr("R0_coop_high", "phi_cx", 0.113)))       # positive branch, cooperation >= 0.75
b80 = ((ex > thr("R0_coop_ge_0.8", "eps_x", 0.401)) & (ell <= thr("R0_coop_ge_0.8", "ell", 0.153))
       & (P["D_max"] <= thr("R0_coop_ge_0.8", "D_max", 0.322)))          # positive branch, cooperation >= 0.8
T["coop_R0_eps_gt_.307"] = med(g("R0", "coop")[ex > 0.307])
T["coop_R0_eps_le_.307"] = med(g("R0", "coop")[ex <= 0.307])
T["coop_R0_P_ge_.75"] = sh(g("R0", "coop") >= .75)
T["coop_R0_P_ge_.75_in_box"] = sh((g("R0", "coop") >= .75)[b75])
T["share_worlds_box75"] = sh(b75)
T["coop_R0_P_ge_.8"] = sh(g("R0", "coop") >= .8)
T["coop_R0_P_ge_.8_in_box"] = sh((g("R0", "coop") >= .8)[b80])
T["coop_R0_P_ge_.8_outside_box"] = sh((g("R0", "coop") >= .8)[~b80])
T["share_worlds_box80"] = sh(b80)
# positive leaf of the R15 tree with a large weight on need (zeta > 0.506, eta > 0.670, g_TA > 0.119)
if "g_TA" in P:
    l3 = ((P["zeta"] > thr("R15_beats_SQ_need", "zeta", 0.506)) & (P["eta_X"] > thr("R15_beats_SQ_need", "eta_X", 0.670))
          & (P["g_TA"] > thr("R15_beats_SQ_need", "g_TA", 0.119)))
    T["R15_leaf3_share_worlds"] = sh(l3)
    T["R15_leaf3_P_need_pos"] = sh((g("R15", "dval_need") > 0)[l3])
# two-condition versions of the boxes (exclusion and localism only), used in the text
b75b = (ex > 0.307) & (ell <= 0.207)
b80b = (ex > 0.401) & (ell <= 0.153)
T["coop_R0_P_ge_.75_outside_box"] = sh((g("R0", "coop") >= .75)[~b75])
T["coop_R0_med_in_box75"] = med(g("R0", "coop")[b75])
T["share_worlds_box75_2"] = sh(b75b)
T["coop_R0_P_ge_.75_in_box75_2"] = sh((g("R0", "coop") >= .75)[b75b])
T["coop_R0_P_ge_.75_outside_box75_2"] = sh((g("R0", "coop") >= .75)[~b75b])
T["coop_R0_med_in_box75_2"] = med(g("R0", "coop")[b75b])
T["share_worlds_box80_2"] = sh(b80b)
T["coop_R0_P_ge_.8_in_box80_2"] = sh((g("R0", "coop") >= .8)[b80b])
T["coop_R0_P_ge_.8_outside_box80_2"] = sh((g("R0", "coop") >= .8)[~b80b])
# how much of each positive result lies inside its box
T["need_pos_share_inside_box"] = float(((g("R0", "dval_need") > 0) & bx).sum() / max((g("R0", "dval_need") > 0).sum(), 1))
T["institutions_pos_share_inside_box"] = float(((inst > 0) & good).sum() / max((inst > 0).sum(), 1))
T["neediest_fifth_pop_share"] = None   # filled below from the geography
# ------------------------------------------------------------------ 6.6 sanctions
for d in ("R0", "R8", "R15"):
    T[f"fail_{d}_mean"] = mean(g(d, "fail"))
    T[f"fail_poor_{d}_mean"] = mean(g(d, "fail_poor"))
    T[f"fail_rich_{d}_mean"] = mean(g(d, "fail_rich"))
    T[f"persist_fail_{d}_mean"] = mean(g(d, "persist_fail"))
    T[f"trap_{d}_mean"] = mean(g(d, "trap"))
for d, k in (("R2", "effort"), ("R2", "effort_u"), ("R2", "coop"), ("R2", "dval"), ("R1", "effort"), ("R1", "coop"),
             ("R1", "dval"), ("R1", "dval_need"), ("R9", "dval"), ("R9", "dval_need"), ("R8", "effort"),
             ("R8", "dval_need"), ("R8", "fail_poor"), ("R2", "completion"), ("R1", "completion")):
    a_, b_ = g("R0", k), g(d, k)
    tol = 1e-9 * (1 + np.abs(b_))
    T[f"R0_vs_{d}_{k}_P_up"] = sh(a_ > b_ + tol)
    T[f"R0_vs_{d}_{k}_P_down"] = sh(a_ < b_ - tol)
    T[f"R0_vs_{d}_{k}_med_diff"] = med(a_ - b_)
T["effort_u_R0_mean"] = mean(g("R0", "effort_u"))
T["effort_u_R2_mean"] = mean(g("R2", "effort_u"))
T["effort_R0_mean"] = mean(g("R0", "effort"))
T["effort_R2_mean"] = mean(g("R2", "effort"))
T["effort_R1_mean"] = mean(g("R1", "effort"))
# ------------------------------------------------------------------ 6.7 law
T["law_on_SQ_beats_law_on_R0_need"] = sh(g("L0", "dval_need") > g("R14", "dval_need"))
T["law_on_SQ_beats_law_on_R0_real"] = sh(g("L0", "dval") > g("R14", "dval"))
T["R14_minus_R0_real_med"] = med(g("R14", "dval") - g("R0", "dval"))
T["L0_minus_SQ_real_med"] = med(g("L0", "dval"))
T["R16_beats_L0_need"] = sh(g("R16", "dval_need") > g("L0", "dval_need"))
T["R16_beats_L0_real"] = sh(g("R16", "dval") > g("L0", "dval"))
T["R15_beats_L0_need"] = sh(g("R15", "dval_need") > g("L0", "dval_need"))
if "p_I" in P:
    pI = P["p_I"]
    T["L0_P_need_pos_pI_lt_.1"] = sh((g("L0", "dval_need") > 0)[pI < 0.1])
    T["L0_P_need_pos_pI_ge_.1"] = sh((g("L0", "dval_need") > 0)[pI >= 0.1])
    T["pI_range"] = [float(pI.min()), float(pI.max())]
# ------------------------------------------------------------------ additional checks (independent review)
T["persist_all3_R0_median"] = med(g("R0", "persist_all3"))
T["cond_PL_t0_median"] = med(g("R0", "cond_PL_t0"))
for lo, hi in ((0, .05), (.05, .25), (.25, .31)):
    s = (bw >= lo) & (bw < hi)
    T[f"cond_top_t2_bw_{lo}_{hi}"] = mean(g("R0", "cond_top_t2")[s])
    T[f"persist_all3_bw_{lo}_{hi}"] = mean(g("R0", "persist_all3")[s])
    T[f"mayor_PL_2036_bw_{lo}_{hi}"] = mean(g("R0", "mayor_PL_2036")[s])
T["div_total_R0_below_SQ"] = sh(g("R0", "div_total") < g("SQ", "div_total"))
T["dval_size_<5k_R10_med"] = med(g("R10", "dval_size_<5k"))
T["dval_size_<5k_R15_med"] = med(g("R15", "dval_size_<5k"))
exc = ~g("R0", "ch_all_parties_gain").astype(bool)
TR = "R0_all_parties_more_legislation"
box = (P["kappa"] <= thr(TR, "kappa", 0.832)) & (P["pi"] > thr(TR, "pi", 0.782)) & (eta > thr(TR, "eta_X", 0.507))
T["all_parties_exceptions_share"] = sh(exc)
T["all_parties_exceptions_in_box"] = sh(box[exc]) if exc.any() else None
T["brokerage_share_R0_med"] = med(1 - g("R0", "ch_leg_effort"))
# concentration of control: party loyalty in the college vote, and how often a party other than PL leads
phi = P["phi_P"]
qp = np.quantile(phi, [1 / 3, 2 / 3])
T["cond_top_t2_phiP_low"] = mean(g("R0", "cond_top_t2")[phi < qp[0]])
T["cond_top_t2_phiP_high"] = mean(g("R0", "cond_top_t2")[phi >= qp[1]])
T["persist_all3_phiP_low"] = mean(g("R0", "persist_all3")[phi < qp[0]])
T["persist_all3_phiP_high"] = mean(g("R0", "persist_all3")[phi >= qp[1]])
for t in range(3):
    T[f"P_other_party_leads_t{t}"] = sh(g("R0", f"cond_top_t{t}") > g("R0", f"cond_PL_t{t}") + 1e-9)
# cooperation by county capacity and term (instrumented run, out/cc2_mech.npz)
mp = os.path.join(ROOT, "out", "cc2_mech.npz")
from cc2_data import Geo
geo = Geo()
o_ = np.argsort(-geo.need)
cp_ = np.cumsum(geo.pop[o_]) / geo.pop.sum()
T["neediest_fifth_pop_share"] = float(geo.pop[o_[cp_ <= 0.2 + 1e-12]].sum() / geo.pop.sum())
if os.path.exists(mp):
    co = np.load(mp)["coop"]
    terc = geo.cap_terc[co["j"]]
    for dsg in ("R0", "R2", "R8", "R1", "R3", "R12"):
        for t in (0, 2):
            for c in (0, 2):
                s = (co["design"] == dsg) & (co["tau"] == t) & (terc == c)
                if s.any():
                    T[f"mech_coop_{dsg}_t{t}_terc{c}"] = float(co["p"][s].mean())
    # cooperation of re-eligible mayors by continuity of the conde's office (Figure 7c)
    for dsg in ("R0", "R1", "R3"):
        s = (co["design"] == dsg) & (co["tl"] == 0)
        bins = np.linspace(0, 1, 11)
        b = np.digitize(co["pcont"][s], bins) - 1
        vals = [(float((bins[i] + bins[i + 1]) / 2), float(co["p"][s][b == i].mean()), int((b == i).sum()))
                for i in range(10) if (b == i).sum() > 200]
        T[f"mech_coop_by_cont_{dsg}"] = vals
json.dump(T, open(os.path.join(ROOT, "out", "cc2_text_numbers.json"), "w"), indent=1)
for k, v in T.items():
    print(k, round(v, 4) if isinstance(v, float) else v)
