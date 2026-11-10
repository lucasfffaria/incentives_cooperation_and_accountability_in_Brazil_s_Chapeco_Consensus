# -*- coding: utf-8 -*-
"""Figure 8: when sanctions work - targets, the bar on reappointment and the trap (Propositions 5 and 7)."""
import os, json
import numpy as np
import matplotlib.pyplot as plt
from scipy.special import expit
from scipy.stats import norm
import figstyle as fs

fs.setup()
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
z = np.load(os.path.join(ROOT, "out", "cc2_worlds.npz"))
fig = plt.figure(figsize=(7.4, 3.25))
axs = [fig.add_axes([0.125, 0.29, 0.20, 0.62]), fig.add_axes([0.41, 0.29, 0.215, 0.62]),
       fig.add_axes([0.80, 0.29, 0.19, 0.62])]
# (a) who fails: base specification (2,000 worlds) and targets on outcome indicators (robustness, 1,000 worlds)
ax = axs[0]
RB = json.load(open(os.path.join(ROOT, "out", "cc2_robust.json")))["outcome_targets"]
rows = [("R0", "absolute targets", None), ("R8", "peer comparison", None),
        ("R0", "absolute targets,\noutcome indicators", RB), ("R8", "peer comparison,\noutcome indicators", RB)]
for i, (d, lab, rb) in enumerate(rows):
    for k, col, off, gl, mk in (("fail_poor", fs.MUSTARD, -0.15, "poorest third", "D"),
                                ("fail_rich", fs.INK, 0.15, "richest third", "o")):
        if rb is None:
            v = z[f"{d}|{k}"]
            lo, hi = np.percentile(v, [5, 95])
            mn = np.mean(v)
        else:
            md_, lo, hi, _, mn = rb[d][k]
        y = len(rows) - 1 - i + off
        ax.plot([lo, hi], [y, y], color=col, lw=1.0)
        ax.scatter(mn, y, s=20, color=col, marker=mk, edgecolor=fs.INK, lw=0.4, zorder=3, label=gl if i == 0 else None)
ax.axhline(1.5, color=fs.AXIS, lw=0.6, ls=(0, (2, 2)))
ax.set_yticks(range(len(rows))[::-1]);
ax.set_yticklabels([r[1] for r in rows], fontsize=6.2)
ax.set_xlim(0, 1);
ax.set_ylim(-0.6, 3.9)
ax.set_xlabel("Share of evaluations failed\n(mean; line: 5th\u201395th pct.)", fontsize=7)
ax.legend(fontsize=6, loc="upper right")
ax.set_title("a  Who fails", fontsize=8)
fs.vgrid(ax)
# (b) the trap: fixed points of completion with and without the bar
ax = axs[1]


def G(c, mu, bar, kap=0.2, Q=0.9, g0=-1.5, beta=0.6, pw=0.9, F=4.0, s=0.4, b=6.0, sn=0.5):
    Pi = norm.cdf((mu + b * c) / sn)
    cont = pw * (kap + (1 - kap) * Pi) if bar else pw
    return Q * expit((g0 + beta * cont * F) / s)


cs = np.linspace(0, 1, 400)
ax.plot(cs, cs, color=fs.MUTED, lw=0.8, ls="--")
mu = -2.5
ax.plot(cs, [G(c, mu, False) for c in cs], color=fs.INK, lw=1.6, label="no bar")
ax.plot(cs, [G(c, mu, True) for c in cs], color=fs.MUSTARD, lw=1.8, label="bar (low-capacity county)")
ax.plot(cs, [G(c, 0.0, True) for c in cs], color=fs.GREY, lw=1.4, ls=":", label="bar (high-capacity county)")
gb = np.array([G(c, mu, True) for c in cs]) - cs
roots = [cs[i] for i in range(len(cs) - 1) if gb[i] * gb[i + 1] < 0]
for r_ in roots:
    ax.scatter(r_, r_, s=24, color=fs.MUSTARD, edgecolor=fs.INK, lw=0.6, zorder=4)
ax.set_xlabel("Completion this term", fontsize=7)
ax.set_ylabel("Completion next term", fontsize=7)
ax.set_xlim(0, 1);
ax.set_ylim(0, 1)
ax.legend(fontsize=5.8, loc="upper left")
ax.set_title("b  The sanction trap (Prop. 7)", fontsize=8)
fs.hgrid(ax)
# (c) what each sanction rule does (share of worlds in which the rule raises the outcome)
ax = axs[2]
comps = [("R2", "bar on reappointment\n(R0 vs no bar)"), ("R1", "reappointment allowed\n(R0 vs one term)"),
         ("R9", "territorial cut\n(R0 vs conde only)"), ("R8", "absolute targets\n(R0 vs peers)")]
outs = [("effort", "conde's effort", fs.INK), ("coop", "cooperation", fs.MUSTARD), ("completion", "completion", fs.GREY),
        ("dval", "real value", fs.SUN), ("dval_need", "need-weighted value", fs.CREAM)]
bal = {}
for ci, (d, lab) in enumerate(comps):
    for oi, (k, ol, col) in enumerate(outs):
        a_, b_ = z[f"R0|{k}"], z[f"{d}|{k}"]
        tol = 1e-9 * (1 + np.abs(b_))
        up, down = np.mean(a_ > b_ + tol), np.mean(a_ < b_ - tol)
        bal[f"{d}|{k}"] = (float(up), float(down))
        y = len(comps) - 1 - ci + (2 - oi) * 0.16
        ax.barh(y, up - down, left=0, height=0.14, color=col, edgecolor=fs.INK, linewidth=0.4, label=ol if ci == 0 else None)
ax.axvline(0, color=fs.INK2, lw=0.8)
ax.set_xlim(-1, 1)
ax.set_yticks(range(len(comps)));
ax.set_yticklabels([c[1] for c in comps][::-1], fontsize=6.0)
ax.set_xlabel("Share of worlds in which the proposal's rule raises\nthe outcome minus share in which it lowers it", fontsize=6.4)
ax.set_ylim(-0.45, 3.45)
ax.legend(fontsize=5.6, loc="upper center", bbox_to_anchor=(0.12, -0.30), ncol=3, handlelength=1.0, frameon=False,
          columnspacing=0.9)
ax.set_title("c  What the sanction rules do", fontsize=8, x=-0.62, ha="left")
fs.vgrid(ax)
json.dump(bal, open(os.path.join(ROOT, "out", "cc2_sanction_balance.json"), "w"), indent=1)
fig.savefig(os.path.join(ROOT, "figs", "fig8_sanctions.png"));
fig.savefig(os.path.join(ROOT, "figs", "fig8_sanctions.pdf"))
print("fig8 done", roots)
