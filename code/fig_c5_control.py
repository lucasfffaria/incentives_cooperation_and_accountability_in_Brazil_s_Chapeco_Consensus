# -*- coding: utf-8 -*-
"""Figure 5: who controls the condes, and for how long (real 2024 colleges, then three simulated terms)."""
import os, json
import numpy as np, pandas as pd
import matplotlib.pyplot as plt
import figstyle as fs
from cc2_data import SEATS

fs.setup()
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
z = np.load(os.path.join(ROOT, "out", "cc2_worlds.npz"))
P = {k[2:]: z[k] for k in z.files if k.startswith("P|")}
E = json.load(open(os.path.join(ROOT, "out", "college_expected.json")))
m = pd.read_csv(os.path.join(ROOT, "data", "derived", "sc_master2.csv"))
fig, axs = plt.subplots(1, 3, figsize=(7.9, 3.0), gridspec_kw=dict(width_ratios=[1.55, 0.95, 1], wspace=0.55))
# (a) real inputs and the data-based party-line benchmark
ax = axs[0]
PARTS = ["PL", "MDB", "PP", "PSD"]
seats = SEATS                                      # deputies elected in 2026 (federations as lists)
may = m.party.value_counts(normalize=True)
popg = m.groupby("party").pop2022.sum() / m.pop2022.sum()
cols = [("Dep.\n2026", {p: seats.get(p, 0) / 16 for p in PARTS}),
        ("Mayors\n2024", {p: float(may.get(p, 0)) for p in PARTS}),
        ("Pop.\ngov.", {p: float(popg.get(p, 0)) for p in PARTS}),
        ("Condes\n1 vote", {p: E["expected_condes_1m1v"].get(p, 0) for p in PARTS}),
        ("County\nmoney", {p: E["money_1m1v"].get(p, 0) for p in PARTS}),
        ("Condes\npop. w.", {p: E["expected_condes_pop"].get(p, 0) for p in PARTS})]
for i, (lab, sh) in enumerate(cols):
    b = 0
    for p in PARTS:
        v = sh[p]
        if v <= 0:
            continue
        ax.bar(i, v, bottom=b, color=fs.PARTY_COLOR.get(p, fs.OTHER), width=0.7, edgecolor="white", lw=0.6)
        if p == "PL":
            ax.text(i, v / 2, f"{100 * v:.0f}", ha="center", va="center", fontsize=6.3, color=fs.INK,
                    fontweight="bold")
        b += v
    ax.bar(i, max(0, 1 - b), bottom=b, color=fs.OTHER, width=0.7, edgecolor="white", lw=0.6)
    ax.bar(i, 1, bottom=0, fill=False, width=0.7, edgecolor=fs.INK2, lw=0.5)          # outline of the stack
ax.set_xticks(range(len(cols)));
ax.set_xticklabels([c[0] for c in cols], fontsize=5.3)
ax.tick_params(axis="x", length=0, pad=2)
ax.set_ylim(0, 1);
ax.set_ylabel("Share", fontsize=7)
from matplotlib.patches import Patch

ax.legend(handles=[Patch(facecolor=fs.PARTY_COLOR[p], edgecolor=fs.INK, lw=0.4, label=fs.plabel(p))
                   for p in ("PL", "MDB", "PP", "PSD")] +
                  [Patch(facecolor=fs.OTHER, edgecolor=fs.INK, lw=0.4, label="Other")], fontsize=5.6, ncol=5, loc="upper center",
          bbox_to_anchor=(0.5, -0.2), handlelength=0.9, columnspacing=0.6)
ax.set_title("a  Inputs and 2027 colleges", fontsize=8)
# (b) three terms: PL and the leading party
ax = axs[1]
for k, (key, lab, c, off) in enumerate((("cond_PL_t", "PL", fs.MUSTARD, -0.12), ("cond_top_t", "Leading party", fs.INK,
                                                                                0.12))):
    for t in range(3):
        v = z[f"R0|{key}{t}"]
        lo, q1, md, q3, hi = np.percentile(v, [5, 25, 50, 75, 95])
        x = t + off
        ax.plot([x, x], [lo, hi], color=c, lw=0.9);
        ax.plot([x, x], [q1, q3], color=c, lw=3.0, solid_capstyle="butt")
        ax.scatter(x, np.mean(v), s=16, color="white", edgecolor=c, lw=1.1, zorder=3, label=lab if t == 0 else None)
ax.axhline(E["expected_condes_1m1v"]["PL"], color=fs.MUSTARD, lw=1.0, ls=":", label="PL, party-line benchmark")
ax.set_xticks([0, 1, 2]);
ax.set_xticklabels(["2027", "2031", "2035"], fontsize=7)
ax.set_ylim(0, 1);
ax.set_ylabel("Share of the 17 condes", fontsize=7)
ax.legend(fontsize=6, loc="upper left")
ax.set_title("b  Control over three terms", fontsize=8)
fs.hgrid(ax)
# (c) persistence by design and the bandwagon
ax = axs[2]
bw = P["beta_bw"]
bins = np.linspace(0, 0.3, 7);
mid = (bins[:-1] + bins[1:]) / 2
for d, lab, c, mk in (("R0", "One vote per mayor", fs.INK, "o"), ("R6", "Population weights", fs.MUSTARD, "s")):
    v = z[f"{d}|persist_all3"]
    md = [np.mean(v[(bw >= bins[i]) & (bw < bins[i + 1])]) for i in range(6)]
    ax.plot(mid, md, color=c, lw=1.6, marker=mk, ms=3.5, mec=fs.INK, mew=0.4, label=lab)
ax.set_ylim(0, 0.4)
ax.set_xlabel("Bandwagon toward the conde's party", fontsize=7)
ax.set_ylabel("Counties held by one party\nin all three terms (share)", fontsize=7)
ax.legend(fontsize=5.8, loc="upper left")
ax.set_title("c  Persistence and bandwagon", fontsize=8)
fs.hgrid(ax)
fig.savefig(os.path.join(ROOT, "figs", "fig5_control.png"));
fig.savefig(os.path.join(ROOT, "figs", "fig5_control.pdf"))
print("fig5 done")
