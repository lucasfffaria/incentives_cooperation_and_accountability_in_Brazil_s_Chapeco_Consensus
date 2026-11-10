# -*- coding: utf-8 -*-
"""Figure 10: what drives the results (grouped Sobol' total effects) and where the proposal adds value."""
import os, json
import numpy as np
import matplotlib.pyplot as plt
import figstyle as fs

fs.setup()
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
z = np.load(os.path.join(ROOT, "out", "cc2_worlds.npz"))
P = {k[2:]: z[k] for k in z.files if k.startswith("P|")}
G = json.load(open(os.path.join(ROOT, "out", "cc2_gsa_R0.json")))
fig = plt.figure(figsize=(7.4, 3.1))
gs = fig.add_gridspec(1, 3, width_ratios=[1.45, 1, 1], wspace=0.55)
ax = fig.add_subplot(gs[0])
outs = [("dval_need", "Need-weighted value"), ("dval", "Real value"), ("coop", "Cooperation"),
        ("reg_share", "Regional share"), ("completion", "Completion"), ("ch_leg_effort", "Legislative effort"),
        ("cond_top_t2", "Party concentration, 2035")]
groups = G["groups"]
gl = {"Chamber": "Chamber", "Relocation": "Relocation", "Projects": "Projects", "Implementation": "Implement.",
      "Cooperation": "Cooperation", "Conde": "Conde", "Municipal": "Municipal", "Diversion": "Diversion",
      "Targets": "Targets", "Need": "Need weight"}
M = np.array([[max(0.0, G["sobol"][o]["ST"][g]) for g in groups] for o, _ in outs])
from matplotlib.colors import LinearSegmentedColormap
cw = LinearSegmentedColormap.from_list("w_yk", ["#ffffff"] + fs.SEQ[1:])
im = ax.imshow(M, cmap=cw, vmin=0, vmax=0.8, aspect="auto")
for i in range(M.shape[0]):
    for j in range(M.shape[1]):
        if M[i, j] >= 0.05:
            rgb = cw(min(M[i, j], 0.8) / 0.8)[:3]
            lum = 0.2126 * rgb[0] + 0.7152 * rgb[1] + 0.0722 * rgb[2]
            ax.text(j, i, f"{M[i, j]:.2f}".lstrip("0"), ha="center", va="center", fontsize=5.6,
                    color="white" if lum < 0.35 else fs.INK)
ax.set_yticks(range(len(outs)));
ax.set_yticklabels([o[1] for o in outs], fontsize=6.4)
ax.set_xticks(range(len(groups)));
ax.set_xticklabels([gl[g] for g in groups], fontsize=6.0, rotation=55, ha="right")
ax.tick_params(length=0)
for s in ax.spines.values():
    s.set_visible(False)
ax.set_title("a  Total-effect indices (proposal)", fontsize=8)


def share_map(ax, x, y, ok, xb, yb, xl, yl, title):
    H = np.full((len(yb) - 1, len(xb) - 1), np.nan)
    for i in range(len(xb) - 1):
        for j in range(len(yb) - 1):
            s = (x >= xb[i]) & (x < xb[i + 1]) & (y >= yb[j]) & (y < yb[j + 1])
            if s.sum() >= 10:
                H[j, i] = ok[s].mean()
    ax.imshow(H, origin="lower", extent=[xb[0], xb[-1], yb[0], yb[-1]], aspect="auto", cmap=fs.CMAP_DIV,
              vmin=0, vmax=1)
    xc = (xb[:-1] + xb[1:]) / 2;
    yc = (yb[:-1] + yb[1:]) / 2
    Hc = np.nan_to_num(H, nan=0.5)
    ax.contour(xc, yc, Hc, levels=[0.5], colors=fs.INK, linewidths=1.0)
    ax.set_xlabel(xl, fontsize=7);
    ax.set_ylabel(yl, fontsize=7)
    ax.set_title(title, fontsize=8)


ax = fig.add_subplot(gs[1])
share_map(ax, P["sig_bar"], P["phi_cx"], z["R0|dval"] > z["D0|dval"], np.linspace(-0.1, 0.3, 9),
          np.linspace(0, 0.3, 7), "Mean net scale economies", "Completion penalty of\nregional projects",
          "b  Counties add value")
ax = fig.add_subplot(gs[2])
share_map(ax, P["sig_bar"], P["zeta"], z["R0|dval_need"] > 0, np.linspace(-0.1, 0.3, 9), np.linspace(0, 1, 9),
          "Mean net scale economies", "Weight on need ($\\zeta$)",
          "c  Proposal beats status quo\n(need-weighted value)")
cax = fig.add_axes([0.92, 0.25, 0.01, 0.5])
sm = plt.cm.ScalarMappable(cmap=fs.CMAP_DIV, norm=plt.Normalize(0, 1))
cb = fig.colorbar(sm, cax=cax);
cb.ax.tick_params(labelsize=6, length=2);
cb.outline.set_linewidth(0.3)
cb.set_label("share of worlds", fontsize=6.5)
fig.savefig(os.path.join(ROOT, "figs", "fig10_discovery.png"));
fig.savefig(os.path.join(ROOT, "figs", "fig10_discovery.pdf"))
print("fig10 done")
