# -*- coding: utf-8 -*-
"""Figure 3: the real status quo (2025 special transfers scaled to the quota) and who loses under per-capita
county budgets."""
import os, json
import numpy as np, pandas as pd
import matplotlib.pyplot as plt
import figstyle as fs
from cc2_data import Geo, PARTIES

fs.setup()
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
geo = Geo()
m = geo.df
a = np.load(os.path.join(ROOT, "data", "derived", "sq_alloc.npz"), allow_pickle=True)
z = np.load(os.path.join(ROOT, "out", "cc2_worlds.npz"))
CL = ["<5k", "5-10k", "10-20k", "20-50k", "50-100k", ">100k"]
LAB = ["<5", "5–10", "10–20", "20–50", "50–100", ">100"]
fig, axs = plt.subplots(1, 3, figsize=(7.4, 3.2), gridspec_kw=dict(width_ratios=[1.05, 0.9, 1.25], wspace=0.55))
# (a) per capita by size class
ax = axs[0]
pc = [m.loc[m.size_class == c, "x_sq"].sum() / m.loc[m.size_class == c, "pop2022"].sum() for c in CL]
nn = [int((m.size_class == c).sum()) for c in CL]
ax.bar(range(6), pc, color=fs.MUSTARD, width=0.62, edgecolor=fs.INK, linewidth=0.4)
avg = m.x_sq.sum() / m.pop2022.sum()
ax.axhline(avg, color=fs.INK2, lw=0.9, ls="--")
ax.text(5.45, avg + 5, f"state average R$ {avg:.0f}", fontsize=6.2, ha="right", va="bottom", color=fs.INK2)
for i, (v, n_) in enumerate(zip(pc, nn)):
    ax.text(i, v + 4, f"{v:.0f}", ha="center", fontsize=6.4, color=fs.INK)
    ax.text(i, -45, f"{n_}", ha="center", fontsize=5.6, color=fs.MUTED)
ax.set_xticks(range(6));
ax.set_xticklabels(LAB, fontsize=5.8, rotation=35)
ax.set_xlabel("Population (thousands); n below", fontsize=6.8, labelpad=8)
ax.set_ylabel("R$ per inhabitant per year", fontsize=7.2)
ax.set_ylim(0, 330);
fs.hgrid(ax)
ax.set_title("a  Amendments today", fontsize=8)
# (b) partisan targeting by deputy (party colour and marker)
MK = {"PL": "o", "MDB": "s", "PSD": "^", "UNIÃO": "D", "CIDADANIA": "v", "PT": "P", "NOVO": "X"}
ax = axs[1]
pix = a["pix_dm"];
dp = a["dep_party"];
low = a["low_pix"]
for k in range(16):
    if low[k]:
        continue
    same = (m.party.values == dp[k])
    own = (pix[k] * same).sum() / pix[k].sum()
    exp = same.mean()
    ax.scatter(exp, own, s=28, color=fs.PARTY_COLOR.get(dp[k], fs.OTHER), marker=MK.get(dp[k], "o"),
               edgecolor=fs.INK, lw=0.5, zorder=3)
ax.plot([0, 1], [0, 1], color=fs.MUTED, lw=0.8, ls="--")
ax.set_xlim(-0.02, 0.4);
ax.set_ylim(-0.02, 1.0)
ax.set_xlabel("Share of municipalities with a\nmayor of the deputy's party", fontsize=7.0)
ax.set_ylabel("Share of the deputy's money\nto those municipalities", fontsize=7.0)
from matplotlib.lines import Line2D

hd = [Line2D([], [], marker=MK[p], ls="", markerfacecolor=fs.PARTY_COLOR[p], markeredgecolor=fs.INK,
             markeredgewidth=0.5, label=fs.plabel(p), markersize=4.5) for p in ("PL", "MDB", "PSD", "UNIÃO", "CIDADANIA")]
ax.legend(handles=hd, fontsize=5.8, loc="upper right", handletextpad=0.2, borderaxespad=0.1)
ax.set_title("b  Partisan targeting", fontsize=8)
fs.hgrid(ax)
# (c) change in value by size class (designs)
ax = axs[2]
des = [("D0", "D0 per capita", fs.GREY, "o"), ("R0", "R0 proposal", fs.MUSTARD, "D"),
       ("R16", "R16 robust + need", fs.INK, "s")]
for di, (d, lab, c, mk) in enumerate(des):
    for i, cl in enumerate(CL):
        v = z[f"{d}|dval_size_{cl}"]
        lo, md, hi = np.percentile(v, [5, 50, 95])
        x = i + (di - 1) * 0.24
        ax.plot([x, x], [lo, hi], color=c, lw=1.2, solid_capstyle="round")
        ax.scatter(x, md, s=16, color=c, marker=mk, zorder=3, edgecolor=fs.INK, lw=0.4, label=lab if i == 0 else None)
ax.axhline(0, color=fs.INK2, lw=0.8)
ax.set_xticks(range(6));
ax.set_xticklabels(LAB, fontsize=5.8, rotation=35)
ax.set_xlabel("Population (thousands)", fontsize=6.8)
ax.set_ylabel("Change in value received (%)", fontsize=7.2)
ax.set_yscale("symlog", linthresh=10);
ax.set_yticks([-50, -25, -10, 0, 10, 25, 50, 100, 200])
ax.set_yticklabels(["−50", "−25", "−10", "0", "10", "25", "50", "100", "200"], fontsize=6.4)
ax.legend(fontsize=5.6, loc="upper left", handletextpad=0.2, ncol=1, frameon=True, facecolor="white",
          edgecolor="none", framealpha=0.95, borderaxespad=0.3)
ax.set_title("c  Change in value", fontsize=8)
fs.hgrid(ax)
fig.savefig(os.path.join(ROOT, "figs", "fig3_statusquo.png"));
fig.savefig(os.path.join(ROOT, "figs", "fig3_statusquo.pdf"))
print("fig3 done")
