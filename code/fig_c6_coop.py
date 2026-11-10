# -*- coding: utf-8 -*-
"""Figure 6: when mayors cooperate (Proposition 4)."""
import os
import numpy as np
import matplotlib.pyplot as plt
import figstyle as fs

fs.setup()
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
z = np.load(os.path.join(ROOT, "out", "cc2_worlds.npz"))
mech = np.load(os.path.join(ROOT, "out", "cc2_mech.npz"))
c = mech["coop"]
fig = plt.figure(figsize=(7.4, 3.25))
axs = [fig.add_axes([0.075, 0.29, 0.215, 0.62]), fig.add_axes([0.445, 0.29, 0.235, 0.62]),
       fig.add_axes([0.775, 0.29, 0.215, 0.62])]
# (a) cooperation against enforcement relative to the stake
ax = axs[0]
r0 = c[c["design"] == "R0"]
x = r0["fut"] + r0["excl"]
bins = np.quantile(x, np.linspace(0, 1, 21))
for msk, lab, col, mk in ((r0["tl"] == 1, "term-limited mayors", fs.MUSTARD, "s"),
                          (r0["tl"] == 0, "re-eligible mayors", fs.INK, "o")):
    xs, ys = x[msk], r0["p"][msk]
    bb = np.quantile(xs, np.linspace(0, 1, 13))
    mx = [np.median(xs[(xs >= bb[i]) & (xs <= bb[i + 1])]) for i in range(12)]
    my = [np.mean(ys[(xs >= bb[i]) & (xs <= bb[i + 1])]) for i in range(12)]
    ax.plot(mx, my, color=col, lw=1.6, marker=mk, ms=3.0, mec=fs.INK, mew=0.4, label=lab)
ax.set_xscale("symlog", linthresh=0.1)
ax.set_xlabel("Enforcement relative to the stake\n(exclusion + future benefits at risk)", fontsize=7)
ax.set_ylabel("Probability of cooperating", fontsize=7)
ax.set_ylim(0, 1);
ax.legend(fontsize=6, loc="lower right")
ax.set_title("a  Enforcement (Prop. 3)", fontsize=8)
fs.hgrid(ax)
# (b) cooperation by type and design
ax = axs[1]
groups = [("coop_el", "Re-eligible"), ("coop_tl", "Term-limited"), ("coop_al", "Conde's party"),
          ("coop_opp", "Other parties"), ("coop_small", "Under 10,000")]
des = [("R0", "Proposal", fs.INK, "o"), ("R1", "One-term conde", fs.GREY, "s"), ("R3", "Binding contracts", fs.MUSTARD, "D"),
       ("R12", "Technical conde", fs.DARKGOLD, "^")]
for di, (d, lab, col, mk) in enumerate(des):
    for gi, (k, gl) in enumerate(groups):
        v = z[f"{d}|{k}"]
        if d == "R12" and k in ("coop_opp", "coop_al"):
            continue
        y = len(groups) - 1 - gi + (1.5 - di) * 0.17
        lo, md, hi = np.percentile(v, [25, 50, 75])
        ax.plot([lo, hi], [y, y], color=col, lw=2.2, solid_capstyle="butt", alpha=0.9)
        ax.scatter(md, y, s=15, color="white", marker=mk, edgecolor=col, lw=1.1, zorder=3, label=lab if gi == 0 else None)
ax.set_yticks(range(len(groups)));
ax.set_yticklabels([g[1] for g in groups][::-1], fontsize=6.5)
ax.set_xlim(0.2, 1.0);
ax.set_xlabel("Cooperation probability (median, IQR)", fontsize=7)
ax.legend(fontsize=5.6, loc="upper center", bbox_to_anchor=(0.4, -0.30), ncol=2, handletextpad=0.1, columnspacing=0.8)
ax.set_title("b  Who cooperates", fontsize=8)
fs.vgrid(ax)
# (c) continuity of the conde's office (re-eligible mayors)
ax = axs[2]
for d, lab, col, ls, mk in (("R0", "Proposal (reappointment\nbarred if targets missed)", fs.INK, "-", "o"),
                            ("R1", "One-term conde", fs.GREY, (0, (4, 2)), "s"),
                            ("R3", "Binding contracts", fs.MUSTARD, "-", "D")):
    cc = c[(c["design"] == d) & (c["tl"] == 0)]
    bb = np.linspace(0, 1, 11)
    mx, my = [], []
    for i in range(10):
        s = (cc["pcont"] >= bb[i]) & (cc["pcont"] < bb[i + 1])
        if s.sum() > 200:
            mx.append((bb[i] + bb[i + 1]) / 2);
            my.append(cc["p"][s].mean())
    ax.plot(mx, my, color=col, lw=1.6, ls=ls, marker=mk, ms=3.0, mec=fs.INK, mew=0.4, label=lab)
ax.set_xlabel("Expected continuity of the conde's office", fontsize=7)
ax.set_ylabel("Cooperation of re-eligible mayors", fontsize=7)
ax.set_ylim(0.4, 1);
ax.legend(fontsize=5.7, loc="lower right")
ax.set_title("c  Horizon", fontsize=8)
fs.hgrid(ax)
fig.savefig(os.path.join(ROOT, "figs", "fig6_cooperation.png"));
fig.savefig(os.path.join(ROOT, "figs", "fig6_cooperation.pdf"))
print("fig6 done")
