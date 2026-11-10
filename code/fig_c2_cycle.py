# -*- coding: utf-8 -*-
"""Figure 2: the repeated county game and the calendar of staggered terms."""
import os
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch
import figstyle as fs

fs.setup()
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
fig = plt.figure(figsize=(7.2, 6.4))
ax = fig.add_axes([0.0, 0.33, 1.0, 0.67]);
ax.set_xlim(0, 100);
ax.set_ylim(0, 64);
ax.set_axis_off()
BOX = dict(boxstyle="round,pad=0.5,rounding_size=1.2", lw=0.8)


def box(x, y, w, h, title, body, fc, ec):
    ax.add_patch(FancyBboxPatch((x, y), w, h, fc=fc, ec=ec, **BOX))
    ax.text(x + 1.2, y + h - 1.6, title, fontsize=7.2, fontweight="bold", color=fs.INK, va="top")
    ax.text(x + 1.2, y + h - 5.4, body, fontsize=6.3, color=fs.INK2, va="top", linespacing=1.3)


def arrow(p0, p1, rad=0.0, color=fs.INK2):
    ax.add_patch(FancyArrowPatch(p0, p1, arrowstyle="-|>", mutation_scale=9, lw=0.9, color=color,
                                 connectionstyle=f"arc3,rad={rad}"))


fcA, ecA = "#fff6d6", fs.MUSTARD
fcB, ecB = "#f1f1f2", fs.GREY
W_, H_ = 29, 14.5
pos = {1: (2, 46), 2: (35.5, 46), 3: (69, 46), 4: (69, 25), 5: (35.5, 25), 6: (2, 25)}
box(*pos[1], W_, H_, "1  Selection",
    "The college of mayors in office elects\nthe conde by plurality: party loyalty,\nretrospective votes for the incumbent;\nthe conde's type and competence", fcA, ecA)
box(*pos[2], W_, H_, "2  Plan and negotiation",
    "The conde proposes regional projects and\nlocal transfers; a majority of mayors must\napprove; the cheapest majority is\ncompensated (Romer-Rosenthal)", fcA, ecA)
box(*pos[3], W_, H_, "3  Cooperation or obstruction",
    "Hosts give land and permits, participants\npay 30% co-financing; private cost shocks;\nhorizon = mayor survival \u00d7 continuity\nof the conde's office; contracts", fcB, ecB)
box(*pos[4], W_, H_, "4  Implementation",
    "Completion depends on pooled capacity,\nsupervision and quality effort,\ncooperation; unfinished works continue\nor are abandoned when the party changes", fcB, ecB)
box(*pos[5], W_, H_, "5  Results and survival",
    "Value, diversion and capture; county\nscore (capacity, delivery, noise); mid-term\nmunicipal elections: re-election, party\nswitching, bandwagon to the conde", fcB, ecB)
box(*pos[6], W_, H_, "6  Reappointment",
    "The new college reappoints or replaces\nthe conde; a missed target bars\nreappointment and may cut the county's\nnext transfers; projects carry over", fcA, ecA)
for a, b_ in ((1, 2), (2, 3)):
    arrow((pos[a][0] + W_ + 0.4, pos[a][1] + H_ / 2), (pos[b_][0] - 0.4, pos[b_][1] + H_ / 2))
arrow((pos[3][0] + W_ / 2, pos[3][1] - 0.4), (pos[4][0] + W_ / 2, pos[4][1] + H_ + 0.4))
for a, b_ in ((4, 5), (5, 6)):
    arrow((pos[a][0] - 0.4, pos[a][1] + H_ / 2), (pos[b_][0] + W_ + 0.4, pos[b_][1] + H_ / 2))
arrow((pos[6][0] + W_ / 2, pos[6][1] + H_ + 0.4), (pos[1][0] + W_ / 2, pos[1][1] - 0.4))
ax.text(50, 41.6, "repeated every term (2027, 2031, 2035)", ha="center", fontsize=6.6, color=fs.MUTED, style="italic")
# Chamber box
ax.add_patch(FancyBboxPatch((2, 6.0), 96, 11.5, fc=fs.CREAM, ec=fs.INK2, **BOX))
ax.text(3.2, 15.6, "Chamber (closed lists, no individual amendments)", fontsize=7.2, fontweight="bold", color=fs.INK,
        va="top")
ax.text(3.2, 11.6, "List-makers rank aspirants by legislative and brokerage skill (selection);  deputies split effort "
                   "between legislation and brokerage (incentives);\n"
                   "a share of the abolished money reappears in discretionary channels (relocation), and deputies of a "
                   "party can broker through its condes.", fontsize=6.3, color=fs.INK2, va="top", linespacing=1.35)
arrow((50, 24.6), (50, 17.9), color=fs.MUTED)
ax.text(51, 21.0, "party control of county money", fontsize=6.2, color=fs.MUTED)
ax.text(1, 63, "a", fontsize=10, fontweight="bold")
# timeline
ax2 = fig.add_axes([0.07, 0.04, 0.9, 0.25])
ax2.set_xlim(2024.5, 2039);
ax2.set_ylim(-0.4, 3.9)
for s in ("left", "top", "right"):
    ax2.spines[s].set_visible(False)
ax2.set_yticks([0.5, 1.5, 2.6]);
ax2.set_yticklabels(["Conde terms", "Mayors' terms", "Elections"], fontsize=7)
ax2.tick_params(axis="y", length=0)
ax2.set_xticks(range(2025, 2040, 2));
ax2.tick_params(axis="x", labelsize=7)
for i, (a, b_) in enumerate(((2025, 2029), (2029, 2033), (2033, 2037), (2037, 2039))):
    ax2.add_patch(plt.Rectangle((a, 1.15), b_ - a - 0.06, 0.7, fc="#dcdcdf" if i % 2 else "#efeff0", ec="none"))
    lab = ["elected 2024 (real)", "elected 2028", "elected 2032", "elected 2036"][i]
    ax2.text(a + 0.15, 1.5, lab, fontsize=6.2, va="center", color=fs.INK2)
for i, (a, b_) in enumerate(((2027, 2031), (2031, 2035), (2035, 2039))):
    ax2.add_patch(plt.Rectangle((a, 0.15), b_ - a - 0.06, 0.7, fc="#ffe08a" if i % 2 else "#fff1bf", ec="none"))
    ax2.text(a + 0.15, 0.5, f"conde term {i + 1}", fontsize=6.2, va="center", color=fs.INK2)
for yr, lab, c, hi in ((2026, "Chamber\n(2026, real)", fs.GREY, False),
                       (2027, "conde elected by the\n2024 mayors", fs.INK, True), (2028, "municipal", fs.MUSTARD, False),
                       (2030, "Chamber", fs.GREY, False), (2031, "college of the\n2028 mayors", fs.INK, True),
                       (2032, "municipal", fs.MUSTARD, False), (2034, "Chamber", fs.GREY, False),
                       (2035, "college of the\n2032 mayors", fs.INK, True), (2036, "municipal", fs.MUSTARD, False)):
    top = 2.95 if hi else 2.4
    ax2.plot([yr, yr], [2.2, top], color=c, lw=1.4)
    ax2.text(yr, top + 0.05, lab, fontsize=5.8, ha="center", va="bottom", color=fs.INK2, linespacing=1.05)
ax2.text(2024.55, 3.9, "b", fontsize=10, fontweight="bold", va="top")
fig.savefig(os.path.join(ROOT, "figs", "fig2_cycle.png"));
fig.savefig(os.path.join(ROOT, "figs", "fig2_cycle.pdf"))
print("fig2 done")
