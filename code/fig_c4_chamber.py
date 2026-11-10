# -*- coding: utf-8 -*-
"""Figure 4: the Chamber - selection by list-makers (Proposition 1), effort by party and relocation (Prop. 2)."""
import os
import numpy as np
import matplotlib.pyplot as plt
import figstyle as fs
from cc2_chamber import r_corr, top_mean
from cc2_data import SEATS

fs.setup()
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
z = np.load(os.path.join(ROOT, "out", "cc2_worlds.npz"))
P = {k[2:]: z[k] for k in z.files if k.startswith("P|")}
fig = plt.figure(figsize=(7.4, 2.9))
axs = [fig.add_axes([0.075, 0.20, 0.215, 0.70]), fig.add_axes([0.455, 0.20, 0.2, 0.70]),
       fig.add_axes([0.745, 0.20, 0.245, 0.70])]
# (a) selection: expected legislative skill of the elected
ax = axs[0]
t0, se, rho = 1.2, 2.0, 0.2
a = top_mean(6, 24)
X = np.linspace(0.02, 2.0, 200)
for sn, c, ls, lab in ((0.5, fs.INK, "-", "list-makers' noise 0.5"), (1.5, fs.MUSTARD, "-", "1.5"),
                       (3.0, fs.GREY, (0, (4, 2)), "3.0")):
    ax.plot(X, r_corr(X * t0, sn, rho) * a, color=c, lw=1.6, ls=ls, label=lab)
ax.axhline(r_corr(t0, se, rho) * a, color=fs.INK2, lw=0.9, ls="--")
ax.text(1.98, r_corr(t0, se, rho) * a + 0.03, "open list", ha="right", fontsize=6.3, color=fs.INK2)
ax.axvline(1.0, color=fs.GRID, lw=0.8)
ax.set_xlabel("X: list-makers' weight on brokerage\nrelative to voters'", fontsize=7)
ax.set_ylabel("Legislative skill of the elected (SD)", fontsize=7)
ax.legend(fontsize=5.9, loc="upper right", handlelength=1.4)
ax.set_title("a  Selection (Proposition 1)", fontsize=8)
fs.hgrid(ax)
# (b) legislative effort: status quo, closed lists, proposal by party
ax = axs[1]
rows = [("Status quo", 1 - P["s0"], fs.GREY), ("Closed lists only", z["CL|ch_leg_effort"], fs.GREY)]
for p in ("PL", "PT", "MDB", "PSD"):
    rows.append((f"Proposal: {fs.plabel(p)}", z[f"R0|eL_party_{p}"], fs.INK))
rows.append(("Proposal + cap on\ndiscretionary channels", z["R13|ch_leg_effort"], fs.MUSTARD))
for i, (lab, v, c) in enumerate(rows):
    lo, q1, md, q3, hi = np.percentile(v, [5, 25, 50, 75, 95])
    y = len(rows) - 1 - i
    ax.plot([lo, hi], [y, y], color=c, lw=0.9)
    ax.plot([q1, q3], [y, y], color=c, lw=3.2, solid_capstyle="butt")
    ax.scatter(md, y, s=18, color="white", edgecolor=c, lw=1.2, zorder=3)
ax.set_yticks(range(len(rows)));
ax.set_yticklabels([r[0] for r in rows][::-1], fontsize=6.4)
ax.set_xlim(0, 1);
ax.set_xlabel("Share of deputies' effort on legislation", fontsize=7)
ax.set_title("b  Effort", fontsize=8)
fs.vgrid(ax)
# (c) relocation
ax = axs[2]
eta = P["eta_X"]
bins = np.linspace(0, 1, 11)
mid = (bins[:-1] + bins[1:]) / 2
oth_seats = {p: s_ for p, s_ in SEATS.items() if p != "PL"}       # seat-weighted, deputies elected in 2026
others = sum(z[f"R0|eL_party_{p}"] * s_ for p, s_ in oth_seats.items()) / sum(oth_seats.values())
for v, lab, c, ls in ((z["CL|ch_leg_effort"], "Closed lists only", fs.GREY, (0, (4, 2))),
                      (z["R0|eL_party_PL"], "Proposal: PL deputies", fs.MUSTARD, "-"),
                      (others, "Proposal: other parties", fs.INK, "-")):
    md = [np.median(v[(eta >= bins[i]) & (eta < bins[i + 1])]) for i in range(10)]
    lo = [np.percentile(v[(eta >= bins[i]) & (eta < bins[i + 1])], 25) for i in range(10)]
    hi = [np.percentile(v[(eta >= bins[i]) & (eta < bins[i + 1])], 75) for i in range(10)]
    ax.fill_between(mid, lo, hi, color=c, alpha=0.18, lw=0)
    ax.plot(mid, md, color=c, lw=1.7, ls=ls, label=lab)
ax.axhline(np.median(1 - P["s0"]), color=fs.INK2, lw=0.8, ls=":")
ax.text(0.02, np.median(1 - P["s0"]) - 0.06, "status quo", fontsize=6.2, color=fs.INK2)
ax.axvspan(0.5, 1.0, color=fs.NEUTRAL, zorder=0)
ax.text(0.75, 0.97, "range suggested by the\n2022\u201323 relocation episode", ha="center", va="top", fontsize=5.8,
        color=fs.INK2)
ax.set_ylim(0, 1);
ax.set_xlim(0, 1)
ax.set_xlabel("η: share of abolished amendment money\nre-created in discretionary channels", fontsize=7)
ax.set_ylabel("Share of effort on legislation", fontsize=7)
ax.legend(fontsize=5.8, loc="lower left", handlelength=1.6)
ax.set_title("c  Relocation (Proposition 2)", fontsize=8)
fs.hgrid(ax)
fig.savefig(os.path.join(ROOT, "figs", "fig4_chamber.png"));
fig.savefig(os.path.join(ROOT, "figs", "fig4_chamber.pdf"))
print("fig4 done")
