# -*- coding: utf-8 -*-
"""Figure 9: the designs compared, in the same worlds and with the same money."""
import os
import numpy as np
import matplotlib.pyplot as plt
import figstyle as fs
from cc2_params import DESIGN_LABEL

fs.setup()
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
z = np.load(os.path.join(ROOT, "out", "cc2_worlds.npz"))
DES = ["D0", "R0", "R1", "R2", "R3", "R4", "R5", "R6", "R7", "R8", "R9", "R10", "R11", "R12", "R13", "R14", "R15",
       "R16", "L0"]
cols = [("dval", "Real value (%)", (-5, 20)), ("dval_need", "Need-weighted value (%)", (-15, 15)),
        ("coop", "Cooperation", (0, 1.03)), ("reg_share", "Regional share", (0, 0.6))]
fig, axs = plt.subplots(1, 4, figsize=(7.4, 4.6), sharey=True, gridspec_kw=dict(wspace=0.12))
n = len(DES)
for ci, (k, lab, lim) in enumerate(cols):
    ax = axs[ci]
    for i, d in enumerate(DES):
        y = n - 1 - i
        if f"{d}|{k}" not in z.files or (d in ("D0", "L0") and k in ("coop", "reg_share")):
            continue
        v = z[f"{d}|{k}"]
        lo, q1, md, q3, hi = np.percentile(v, [5, 25, 50, 75, 95])
        col = fs.MUSTARD if d == "R0" else (fs.INK if d in ("R15", "R16") else (fs.LIGHTGREY if d in ("D0", "L0") else
                                                                                   fs.GREY))
        ax.plot([lo, hi], [y, y], color=col, lw=0.8)
        ax.plot([q1, q3], [y, y], color=col, lw=3.0, solid_capstyle="butt")
        ax.scatter(md, y, s=14, color="white", edgecolor=col, lw=1.0, zorder=3)
    if k in ("dval", "dval_need"):
        ax.axvline(0, color=fs.INK, lw=0.8)
    md0 = np.median(z[f"R0|{k}"])
    ax.axvline(md0, color=fs.MUSTARD, lw=0.9, ls="--")
    ax.set_xlim(*lim)
    ax.set_title(lab, fontsize=7.2, loc="center")
    ax.tick_params(axis="x", labelsize=6.5)
    fs.vgrid(ax)
axs[0].set_yticks(range(n))
axs[0].set_yticklabels([f"{d}  {DESIGN_LABEL[d]}" for d in DES][::-1], fontsize=6.4)
fig.savefig(os.path.join(ROOT, "figs", "fig9_designs.png"));
fig.savefig(os.path.join(ROOT, "figs", "fig9_designs.pdf"))
print("fig9 done")
