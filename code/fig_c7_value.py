# -*- coding: utf-8 -*-
"""Figure 7: regional projects, completion and where the value comes from (Proposition 3)."""
import os, json
import numpy as np
import matplotlib.pyplot as plt
import figstyle as fs

fs.setup()
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
z = np.load(os.path.join(ROOT, "out", "cc2_worlds.npz"))
mech = np.load(os.path.join(ROOT, "out", "cc2_mech.npz"))
pr = mech["proj"]
M12 = 12 * 595.2e6
fig = plt.figure(figsize=(7.4, 3.0))
axs = [fig.add_axes([0.065, 0.16, 0.235, 0.74]), fig.add_axes([0.435, 0.16, 0.175, 0.74]),
       fig.add_axes([0.80, 0.16, 0.19, 0.74])]
# (a) the completion hurdle
ax = axs[0]
q = np.linspace(0.25, 1, 200)
for vbar, ls, lab in ((0.72, "--", "local value 0.72"), (0.80, "-", "0.80"), (0.88, ":", "0.88")):
    dc, vinc, ab, bd, f = 0.07, 0.3, 0.3, 0.8, 0.95
    qe = q + (1 - q) * (1 - ab) * q * bd
    sw = (1 - q) * ((1 - ab) * (1 - q) + ab) * vinc
    ax.plot(q, f * (vbar / (1 - dc) - sw) / qe - 1, color=fs.INK2, lw=1.1, ls=ls, label=lab)
t = pr[(pr["design"] == "R12")]
rng = np.random.default_rng(0)
sub = rng.choice(len(t), 2500, replace=False)
tt = t[sub]
ax.scatter(tt["q"][tt["sel"] == 0], tt["sig"][tt["sel"] == 0], s=2.5, color=fs.LIGHTGREY, alpha=0.6, label="not chosen",
           rasterized=True)
ax.scatter(tt["q"][tt["sel"] == 1], tt["sig"][tt["sel"] == 1], s=2.5, color=fs.MUSTARD, alpha=0.7, label="chosen",
           rasterized=True)
ax.set_xlim(0.25, 1);
ax.set_ylim(-0.5, 0.9)
ax.set_xlabel("Expected completion", fontsize=7)
ax.set_ylabel("Net scale economies of the project", fontsize=7)
ax.legend(fontsize=5.6, loc="upper right", markerscale=3, handlelength=1.5, frameon=True, facecolor="white",
          edgecolor="none", framealpha=0.92)
ax.set_title("a  Completion hurdle (Prop. 4)", fontsize=8)
fs.hgrid(ax)
# (b) regional investment and completion by design
ax = axs[1]
des = [("R0", "Proposal"), ("R1", "One-term conde"), ("R3", "Contracts"), ("R4", "Co-branding"),
       ("R5", "No co-financing"), ("R12", "Technical conde"), ("R14", "+ managerial law"), ("R15", "Robust variant")]
for i, (d, lab) in enumerate(des):
    y = len(des) - 1 - i
    for k, col, off in (("reg_share", fs.INK, 0.15), ("completion", fs.MUSTARD, -0.15)):
        v = z[f"{d}|{k}"]
        lo, md, hi = np.percentile(v, [25, 50, 75])
        ax.plot([lo, hi], [y + off, y + off], color=col, lw=2.4, solid_capstyle="butt", alpha=0.85)
        ax.scatter(md, y + off, s=12, color="white", edgecolor=col, lw=1.0, zorder=3)
ax.set_yticks(range(len(des)));
ax.set_yticklabels([d[1] for d in des][::-1], fontsize=6.4)
ax.set_xlim(0, 1)
ax.text(0.02, len(des) - 0.45, "regional share of county money", color=fs.INK, fontsize=5.8)
ax.text(0.98, -0.75, "completion of projects", color=fs.DARKGOLD, fontsize=5.8, ha="right")
ax.set_ylim(-1, len(des))
ax.set_xlabel("Share (median, IQR)", fontsize=7)
ax.set_title("b  Investment, completion", fontsize=8)
fs.vgrid(ax)
# (c) where the value comes from: proposal vs status quo (means across worlds, % of status-quo value)
ax = axs[2]
vsq, vd0, vr0 = z["SQ|val"], z["D0|val"], z["R0|val"]
vbar = vd0 / M12                                             # value per real of local money (no counties)
pct = lambda x: 100 * np.mean(x / vsq)
comp = [("Per-capita reallocation", pct(vd0 - vsq)),
        ("Regional projects: value", pct(z["R0|sh_reg_value"] * M12)),
        ("Local value forgone", pct(-vbar * z["R0|sh_reg_cost"] * M12)),
        ("Municipal co-financing", pct(-vbar * z["R0|sh_cofin_paid"] * M12)),
        ("County administration", pct(-vbar * z["R0|sh_admin"] * M12))]
resid = pct(vr0 - vsq) - sum(c_[1] for c_ in comp)
comp.append(("Other, net", resid))
total = pct(vr0 - vsq)
cum = 0
n_ = len(comp)
for i, (lab, v) in enumerate(comp):
    y = n_ - i
    col = fs.MUSTARD if v >= 0 else fs.GREY
    ax.barh(y, v, left=cum, color=col, height=0.62, edgecolor=fs.INK, linewidth=0.4)
    ax.text(max(cum, cum + v) + 0.4, y, f"{v:+.1f}".replace("-", "\u2212"), va="center", fontsize=6.0, color=fs.INK)
    if i < n_ - 1:
        ax.plot([cum + v, cum + v], [y - 0.31, y - 0.69], color=fs.MUTED, lw=0.6)
    cum += v
ax.barh(0, total, color=fs.INK, height=0.62)
ax.text(total + 0.4, 0, f"{total:+.1f}".replace("-", "\u2212"), va="center", fontsize=6.2, color=fs.INK)
ax.axvline(0, color=fs.INK2, lw=0.7)
ax.set_yticks(range(n_ + 1));
ax.set_yticklabels(["Proposal vs status quo"] + [c_[0] for c_ in comp][::-1], fontsize=6.2)
ax.set_xlabel("% of status-quo value (mean across worlds)", fontsize=6.8)
ax.set_xlim(min(-1, total - 3), 17)
ax.set_title("c  Sources of value", fontsize=8, x=-0.55, ha="left")
fs.vgrid(ax)
fig.savefig(os.path.join(ROOT, "figs", "fig7_value.png"));
fig.savefig(os.path.join(ROOT, "figs", "fig7_value.pdf"))
json.dump({lab.replace("\n", " "): float(v) for lab, v in comp} | {"total": float(total)},
          open(os.path.join(ROOT, "out", "cc2_value_decomp.json"), "w"), indent=1)
print("fig7 done", {lab.replace(chr(10), ' '): round(v, 2) for lab, v in comp}, round(total, 2))
