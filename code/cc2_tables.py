# -*- coding: utf-8 -*-
"""Tables of the article and of the Supplementary Material, computed from the outputs in out/ and written to
out/tables/ as Markdown tables, one file per table, named after its number (table2.md is Table 2)."""
import os, json
from decimal import Decimal, ROUND_HALF_UP
import numpy as np
from cc2_params import PRIORS, NAMES, DESIGNS, DESIGN_LABEL, GROUPS

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT, TAB = os.path.join(ROOT, "out"), os.path.join(ROOT, "out", "tables")
os.makedirs(TAB, exist_ok=True)
z = np.load(os.path.join(OUT, "cc2_worlds.npz"))
P = {k[2:]: z[k] for k in z.files if k.startswith("P|")}
N = json.load(open(os.path.join(OUT, "cc2_numbers.json")))


def H(x, nd=0, plus=False):
    """Round half up (on the shortest decimal representation of x) and format with nd decimals; minus sign as −."""
    d = Decimal(repr(float(x))).quantize(Decimal(1).scaleb(-nd), rounding=ROUND_HALF_UP)
    if d == 0:
        d = abs(d)
    s_ = f"{d:f}"
    if plus and d > 0:
        s_ = "+" + s_
    return s_.replace("-", "−")


def nd_of(fmt):
    return int(fmt.split(".")[1][0]) if "." in fmt else 0


def q(a, fmt="{:.2f}", scale=1.0):
    a = np.asarray(a) * scale
    md, lo, hi = np.percentile(a, [50, 5, 95])
    k = nd_of(fmt)
    return f"{H(md, k)} [{H(lo, k)}, {H(hi, k)}]"


def write(name, header, rows, note=None):
    lines = ["| " + " | ".join(header) + " |", "|" + "|".join("---" for _ in header) + "|"]
    for r in rows:
        lines.append("| " + " | ".join(str(x) for x in r) + " |")
    txt = "\n".join(lines) + "\n"
    if note:
        txt += "\n" + note + "\n"
    open(os.path.join(TAB, f"table{name}.md"), "w", encoding="utf-8").write(txt)


g = lambda d, k: z[f"{d}|{k}"]
pct = lambda a: H(100 * np.mean(a), 0) + "%"
above = lambda a, b: a > b + 1e-9 * (1 + np.abs(b))     # same tie rule as cc2_analyze.py
# ------------------------------------------------------------------ Table 3: scorecard of the proposal
rows = [
    ["Share of deputies' effort on legislation", q(1 - P["s0"]), "–", q(g("R0", "ch_leg_effort")),
     pct(g("R0", "ch_leg_effort") > 1 - P["s0"]), "analytical (Proposition 2)"],
    ["… with closed lists only", q(1 - P["s0"]), "–", q(g("CL", "ch_leg_effort")),
     pct(g("CL", "ch_leg_effort") > 1 - P["s0"]), "analytical (Proposition 2)"],
    ["Legislative skill of the elected (SD)", q(g("SQ", "ch_leg_skill")), "–", q(g("R0", "ch_leg_skill")),
     pct(g("R0", "ch_leg_skill") > g("SQ", "ch_leg_skill")), "analytical (Proposition 1)"],
    ["Share of condes from PL, 2027; 2035 (mean)", "–", "–",
     H(100 * np.mean(g('R0', 'cond_PL_t0'))) + "%; " + H(100 * np.mean(g('R0', 'cond_PL_t2'))) + "% (party line: 53%)",
     "–", "data-based and conditional"],
    ["Counties held by one party for three terms", "–", "–", q(g("R0", "persist_all3")), "–",
     "conditional ($\\beta_{bw}$, $\\phi_P$)"],
    ["Population-weighted Gini of per-capita value", q(g("SQ", "gini")), q(g("D0", "gini")), q(g("R0", "gini")),
     pct(g("R0", "gini") < g("SQ", "gini")), "data-based, conditional (η)"],
    ["Value received by the neediest fifth of the population, relative to its population share",
     q(g("SQ", "need_top20_share")), q(g("D0", "need_top20_share")), q(g("R0", "need_top20_share")),
     pct(g("R0", "need_top20_share") > g("SQ", "need_top20_share")), "data-based, conditional (η)"],
    ["Municipalities that receive less value (%)", "–", q(g("D0", "lose_mun"), "{:.0f}", 100),
     q(g("R0", "lose_mun"), "{:.0f}", 100), "–", "data-based"],
    ["Share of county money in regional projects (%)", "–", "0", q(g("R0", "reg_share"), "{:.1f}", 100),
     "–", "conditional ($\\bar\\sigma$, $\\bar s$, $\\phi_{cx}$)"],
    ["Completion of regional projects (%)", "–", "–", q(g("R0", "completion"), "{:.0f}", 100), "–",
     "conditional"],
    ["Cooperation probability of participating mayors", "–", "–", q(g("R0", "coop")), "–",
     "analytical (Proposition 3)"],
    ["Diversion and capture (R$ million per year)", q(g("SQ", "div_total") / 1e6, "{:.1f}"),
     q(g("D0", "div_total") / 1e6, "{:.1f}"), q(g("R0", "div_total") / 1e6, "{:.1f}"),
     pct(g("R0", "div_total") < g("SQ", "div_total")), "conditional"],
    ["Real value delivered (% change)", "–", q(g("D0", "dval"), "{:.1f}"), q(g("R0", "dval"), "{:.1f}"),
     pct(g("R0", "dval") > 0), "conditional (σ̄, ν, η)"],
    ["Need-weighted value (% change)", "–", q(g("D0", "dval_need"), "{:.1f}"), q(g("R0", "dval_need"), "{:.1f}"),
     pct(g("R0", "dval_need") > 0), "conditional (ζ, η, σ̄)"],
]
write("3", ["Indicator", "Status quo", "Per-capita transfers (D0)", "Proposal (R0)", "R0 better (share of worlds)",
            "Type of result"], rows)
# ------------------------------------------------------------------ Table 2: designs
DEF = {
    "SQ": "Open list; individual amendments with the real 2025 geography",
    "CL": "Closed lists; amendments kept",
    "D0": "Closed lists; amendments abolished; per-capita transfers to municipalities; no counties",
    "R0": "Closed lists; abolition; per-capita county budgets; plurality college (one vote per mayor); majority "
          "approval; reappointment barred if targets are missed; 30% municipal co-financing; absolute targets; "
          "failing counties lose a share of new money",
    "R1": "R0 with a single term for the conde", "R2": "R0 without the target bar on reappointment",
    "R3": "R0 with binding consortium contracts", "R4": "R0 with co-branding of regional projects",
    "R5": "R0 without municipal co-financing", "R6": "R0 with population-weighted college and approval",
    "R7": "R0 with a dual majority (mayors and population) to approve the plan",
    "R8": "R0 with targets relative to peers of similar capacity", "R9": "R0 with sanctions on the conde only",
    "R10": "R0 with a need-based split between counties",
    "R11": "R0 with a one-third bonus to counties whose conde is aligned with the federal government",
    "R12": "R0 with a technical conde (no party; values the money at face value; reappointed if and only if the county meets its targets)",
    "R13": "R0 with a cap on residual discretionary channels",
    "R14": "R0 with the managerial law (technical assistance and inspection)",
    "R15": "R0 with contracts, co-branding, dual majority, peer targets, sanctions on the conde only and the "
           "managerial law",
    "R16": "R15 with a need-based split between counties",
    "L0": "Status quo with the managerial law",
}
write("2", ["Design", "Name", "Definition"], [[d, DESIGN_LABEL[d], DEF[d]] for d in DESIGNS])
# ------------------------------------------------------------------ Table S4: parameters
rows = []
for gname in GROUPS:
    for n in NAMES:
        lo, hi, grp, desc, src = PRIORS[n]
        if grp != gname:
            continue
        rows.append([f"`{n}`", grp, desc, f"[{lo:g}, {hi:g}]".replace("-", "−"), src])
write("S4", ["Parameter", "Group", "Description", "Prior (uniform)", "Source or anchor"], rows)
# ------------------------------------------------------------------ Table S6: all designs
keys = [("dval", "Real value (%)", "{:.1f}", 1), ("dval_need", "Need-weighted value (%)", "{:.1f}", 1),
        ("reg_share", "Regional share (%)", "{:.0f}", 100), ("completion", "Completion (%)", "{:.0f}", 100),
        ("coop", "Cooperation", "{:.2f}", 1), ("lose_mun", "Losing municipalities (%)", "{:.0f}", 100)]
rows = []
for d in DESIGNS:
    if d in ("SQ",):
        continue
    r = [f"{d} {DESIGN_LABEL[d]}"]
    for k, lab, fmt, sc in keys:
        if f"{d}|{k}" in z.files and not (d in ("CL", "L0", "D0") and k in ("reg_share", "completion", "coop")):
            md = np.median(g(d, k)) * sc
            r.append(H(md, nd_of(fmt)))
        else:
            r.append("–")
    r.append(pct(g(d, "dval") > 0) if d != "CL" else "–")
    r.append(pct(g(d, "dval_need") > 0) if d != "CL" else "–")
    r.append(pct(above(g(d, "dval_need"), g("R0", "dval_need"))) if d not in ("R0", "CL") else "–")
    rows.append(r)
write("S6", ["Design"] + [k[1] for k in keys] + ["Worlds: real value up", "Worlds: need-weighted up",
                                                  "Worlds: better than R0 (need-weighted)"], rows)
# ------------------------------------------------------------------ Table S9: Sobol
G = json.load(open(os.path.join(OUT, "cc2_gsa_R0.json")))
outs = [("dval_need", "Need-weighted value"), ("dval", "Real value"), ("coop", "Cooperation"),
        ("reg_share", "Regional share"), ("completion", "Completion"), ("ch_leg_effort", "Legislative effort"),
        ("cond_top_t2", "Party concentration (2035)"), ("persist_fail", "Persistence of failure")]
rows = []
for o, lab in outs:
    S = G["sobol"][o]
    r = [lab]
    for gname in G["groups"]:
        st, ci = S["ST"][gname], S["ST_ci"][gname]
        r.append(H(max(st, 0), 2) if st >= 0.005 else "0")
    rows.append(r)
G15p = os.path.join(OUT, "cc2_gsa_R15.json")
groups = list(G["groups"])
note15 = ""
if os.path.exists(G15p):
    G15 = json.load(open(G15p))
    groups = groups + [g for g in G15["groups"] if g not in groups]
    rows = [r + ["–"] * (len(groups) - len(G["groups"])) for r in rows]
    for o, lab in outs[:5]:
        S = G15["sobol"][o]
        r = [f"R15: {lab.lower()}"]
        for gname in groups:
            st = S["ST"].get(gname, 0.0)
            r.append(H(max(st, 0), 2) if st >= 0.005 else "0")
        rows.append(r)
    note15 = (f" Rows marked R15 refer to the robust variant, whose sensitivity analysis also varies the parameters "
              f"of the managerial law (LRG) and of its design elements; N = {G15['N']}, "
              f"{G15['N'] * (len(G15['groups']) + 2):,} runs.")
write("S9", ["Output"] + list(groups), rows,
      note=f"*Note.* Total-effect indices (Jansen estimator) for the proposal as stated (R0) relative to the status "
           f"quo, N = {G['N']} base samples per matrix, {G['N'] * (len(G['groups']) + 2):,} model runs; bootstrap "
           f"95% intervals in the replication files." + note15)
# ------------------------------------------------------------------ Table S8: robustness
Rb = json.load(open(os.path.join(OUT, "cc2_robust.json")))
lab = {"main_1000": "Main specification (1,000 worlds)", "sq_pooled": "Status quo: pooled Pix geography",
       "sq_health_half": "Status quo: half of each quota by population (health)",
       "macro_regions": "Counties: 8 health macro-regions", "party_line_college": "Party-line college voting",
       "strong_bandwagon_free_tilt": "Bandwagon above the prior ($\\beta_{bw}$ from $U[0.3, 0.6]$), costless tilting",
       "no_capacity_gradient": "No capacity gradient in completion (ν = 0)",
       "sq_pooled_low": "Status quo: three low users with the pooled geography",
       "sq_chamber2026": "Status quo: the deputies elected in 2026",
       "outcome_targets": "Targets on outcome indicators"}
ORDER = ["main_1000", "sq_pooled", "sq_pooled_low", "sq_health_half", "sq_chamber2026", "macro_regions",
         "party_line_college", "strong_bandwagon_free_tilt", "no_capacity_gradient", "outcome_targets"]
rows = []
for k in ORDER:
    if k not in Rb:
        continue
    v = dict(Rb[k])
    if k == "main_1000" and "main_targets_pairs" in Rb:      # same worlds and random numbers, base targets
        v["R8"] = Rb["main_targets_pairs"]["R8"]
    for d in ("D0", "R0", "R6", "R8", "R15"):
        if d not in v:
            continue
        s = v[d]
        cty = d != "D0"
        rows.append([lab[k], d, H(s['dval'][0], 1), H(s['dval_need'][0], 1),
                     H(100 * s['dval_need'][3]) + "%", H(s['coop'][0], 2) if cty else "–",
                     H(100 * s['reg_share'][0]) if cty else "–",
                     H(100 * s['cond_PL_t0'][4]) + "%; " + H(100 * s['cond_PL_t2'][4]) + "%" if cty else "–",
                     H(100 * s['persist_all3'][4]) + "%" if cty else "–",
                     H(100 * s['fail_poor'][4]) + "%; " + H(100 * s['fail_rich'][4]) + "%" if cty else "–"])
write("S8", ["Variant", "Design", "Real value (%)", "Need-weighted value (%)", "Worlds: need-weighted up",
             "Cooperation", "Regional share (%)", "PL condes, 2027; 2035 (mean)",
             "Counties held by one party for three terms (mean)",
             "Evaluations failed, poorest; richest third (mean)"], rows,
      note="*Note.* Each variant is run over 1,000 worlds with the parameter draws of the first 1,000 worlds of the "
           "main experiment and its own random numbers; the main specification is re-run in the same way for "
           "comparison (its R8 row comes from a run of R0, R2 and R8 with the same draws and random numbers). "
           "Medians across worlds unless stated otherwise. With targets on outcome indicators, the conde's "
           "delivery accounts for 0.3%–3.3% of the variance of the county score and noise for 2%–20%.")
# ------------------------------------------------------------------ Table S5: calibration checks
Cc = json.load(open(os.path.join(OUT, "cc2_calibration_checks.json")))
rows = [[k, f"{H(v['model'][1], 2)} [{H(v['model'][0], 2)}, {H(v['model'][2], 2)}]",
         f"{H(v['data'][0], 2)}; {H(v['data'][1], 2)}"] for k, v in Cc.items()]
write("S5", ["Moment", "Model, status quo (median [5th, 95th])", "Santa Catarina (two cycles)"], rows)
# ------------------------------------------------------------------ Table S7: paired comparisons with R0
pairs = N["pairs_vs_R0"]
rows = []
for d in ("R1", "R2", "R3", "R4", "R5", "R6", "R7", "R8", "R9", "R10", "R11", "R12", "R13", "R14", "R15", "R16"):
    r = [f"{d} {DESIGN_LABEL[d]}"]
    for k in ("dval", "dval_need", "coop", "completion"):
        md, lo, hi, pp = pairs[d][k]
        sc = 1 if k.startswith("dval") else 1
        r.append(f"{H(md, 2, plus=True)} ({H(100 * pp)}%)")
    rows.append(r)
write("S7", ["Design", "Δ real value (pp)", "Δ need-weighted value (pp)", "Δ cooperation", "Δ completion"], rows,
      note="*Note.* Median paired difference with R0 in the same world; in parentheses, the share of worlds in which "
           "the design is above R0.")
print("tables written:", sorted(os.listdir(TAB)))
# ------------------------------------------------------------------ Table S10: real-data colleges by county
C = json.load(open(os.path.join(OUT, "real_colleges.json")))
PL_NAME = {"NOVO": "Novo", "UNIÃO": "União Brasil", "CIDADANIA": "Cidadania", "REPUBLICANOS": "Republicanos",
           "PODEMOS": "Podemos"}
num = json.load(open(os.path.join(OUT, "region_numbers.json")))
bz = {b["region"]: b for b in C["banzhaf"]}
rows = []
for r in sorted(C["regions"], key=lambda r: num[r["region"]]):
    ties = [PL_NAME.get(t, t) for t in C["ties_1m1v"][r["region"]]]
    p1 = " / ".join(ties) + (" (tie)" if len(ties) > 1 else "") + f", {H(100 * r['share_1m1v'])}% of mayors"
    pp = f"{PL_NAME.get(r['plur_pop'], r['plur_pop'])}, {H(100 * r['share_pop'])}% of population"
    b = bz[r["region"]]
    rows.append([num[r["region"]], r["region"], r["n"], f"{r['polo']} ({H(100 * r['polo_pop_share'])}%)", p1, pp,
                 f"{H(b['banzhaf_1m1v'], 3)} / {H(b['banzhaf_dual'], 2)} / {H(b['banzhaf_pop'], 2)}"])
write("S10", ["#", "County (health region)", "Municipalities", "Largest city (share of population)",
             "Plurality, one mayor one vote", "Plurality, population-weighted",
             "Banzhaf power of largest city: one vote / dual / population"], rows)
print("table S10 written")
