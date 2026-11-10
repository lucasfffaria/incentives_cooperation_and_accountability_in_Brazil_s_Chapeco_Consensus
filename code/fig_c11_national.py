# -*- coding: utf-8 -*-
"""Figure 11 (real data): winners and losers of a national per-capita rule."""
import os, json
import numpy as np, pandas as pd
import matplotlib.pyplot as plt
import figstyle as fs

fs.setup()
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
N = pd.read_csv(os.path.join(ROOT, "out", "national_accounting.csv"), index_col=0).sort_values("change_dep")
NA = json.load(open(os.path.join(ROOT, "out", "national_accounting.json")))
fig, ax = plt.subplots(figsize=(7.0, 4.4))
y = np.arange(len(N))
ax.barh(y, 100 * N.change_dep, color=[fs.GREY if v < 0 else fs.MUSTARD for v in N.change_dep], height=0.7,
        edgecolor=fs.INK, linewidth=0.3)
for yi, (st, r) in zip(y, N.iterrows()):
    v = 100 * r.change_dep
    ax.text(v + (2 if v >= 0 else -2), yi, f"{int(r.seats)}", va="center", ha="left" if v >= 0 else "right",
            fontsize=5.8, color=fs.INK2)
ax.set_yticks(y);
ax.set_yticklabels(N.index, fontsize=6.6)
ax.tick_params(axis="y", length=0, labelcolor=fs.INK2)
ax.axvline(0, color=fs.INK, lw=0.7)
ax.set_xlabel("Change in deputies' individual amendments per inhabitant under a national per-capita rule (%)")
fs.vgrid(ax)
ax.set_xlim(-95, 75)
ax.spines["left"].set_visible(False)
ax.text(-93, 11.5, f"{NA['states_losing_dep']} states lose: {NA['seats_in_losing_states_dep']} of 513 deputies\n"
                   f"and {NA['senators_in_losing_states_dep']} of 81 senators", fontsize=7, color=fs.INK2, va="center")
ax.text(73, len(N) - 7.5, f"{27 - NA['states_losing_dep']} states gain: {513 - NA['seats_in_losing_states_dep']} "
                          f"deputies\nand {81 - NA['senators_in_losing_states_dep']} senators", fontsize=7,
        color=fs.DARKGOLD, va="center", ha="right")
ax.set_title("Who would lose if the amendment money were shared per capita? (numbers: seats in the Chamber)",
             fontsize=8.5)
fig.savefig(os.path.join(ROOT, "figs", "fig11_national.png"));
fig.savefig(os.path.join(ROOT, "figs", "fig11_national.pdf"))
print("fig11 done")
