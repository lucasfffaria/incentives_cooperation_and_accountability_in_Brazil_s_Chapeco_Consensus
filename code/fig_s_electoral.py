# -*- coding: utf-8 -*-
"""Supplementary figure: the electoral connection in Santa Catarina (2022 and 2026 TSE votes, 2025 special
transfers). (a) Where the thirteen deputies who used special transfers sent the money, by their share of the
municipality's 2022 vote; (b) the 2026 vote share against the 2025 transfers, net of deputy and municipality fixed
effects and of the 2022 share (binned). Writes figs/figS6_electoral.(png|pdf)."""
import os, json
import numpy as np, pandas as pd
import matplotlib.pyplot as plt
import figstyle as fs
from targeting import vote_matrix

fs.setup()
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DER, OUT, FIG = (os.path.join(ROOT, "data", "derived"), os.path.join(ROOT, "out"), os.path.join(ROOT, "figs"))
m = pd.read_csv(os.path.join(DER, "sc_master2.csv"))
a = np.load(os.path.join(DER, "sq_alloc.npz"), allow_pickle=True)
E = json.load(open(os.path.join(OUT, "electoral_connection.json")))
names = [str(x) for x in a["dep_names"]]
pix, low, dparty = a["pix_dm"], a["low_pix"], [str(x) for x in a["dep_party"]]
pop = m.pop2022.values.astype(float)
V22, T22 = vote_matrix(m.ibge_id.values, 2022, names)
fig, axs = plt.subplots(1, 2, figsize=(7.2, 2.9), gridspec_kw=dict(wspace=0.38))
# (a) money per inhabitant by the deputy's local vote share (deciles), co-partisan mayor or not
ax = axs[0]
rows = []
for d in np.where(~low)[0]:
    vs = V22[d] / np.maximum(T22, 1)
    same = (m.party.values == dparty[d])
    for j in range(len(pop)):
        rows.append((vs[j], pix[d, j], pop[j], same[j]))
D = pd.DataFrame(rows, columns=["vs", "pix", "pop", "same"])
D["bin"] = pd.qcut(D.vs, 10, labels=False, duplicates="drop")
for flag, lab, c, mk in ((False, "mayor of another party", fs.INK, "o"), (True, "mayor of the deputy's party", fs.MUSTARD, "D")):
    g = D[D.same == flag].groupby("bin")
    x = 100 * g.vs.median()
    y = g.pix.sum() / g["pop"].sum()
    ax.plot(x, y, color=c, lw=1.5, marker=mk, ms=3.6, mec=fs.INK, mew=0.4, label=lab)
ax.set_xscale("log")
ax.set_xticks([0.1, 1, 10]);
ax.set_xticklabels(["0.1", "1", "10"])
ax.xaxis.set_minor_formatter(plt.NullFormatter())
ax.set_xlabel("Deputy's share of the municipality's 2022 vote (%, deciles)", fontsize=7)
ax.set_ylabel("2025 special transfers from the deputy\n(R$ per inhabitant)", fontsize=7)
ax.legend(fontsize=6, loc="upper left")
b = E["ppml"]
ax.text(0.03, 0.74, f"PPML elasticity to the vote share {b['lvs'][0]:.2f} (s.e. {b['lvs'][1]:.2f});\n"
                    f"co-partisan mayor: ×{np.exp(b['same'][0]):.1f}", transform=ax.transAxes, ha="left",
        va="top", fontsize=5.8, color=fs.INK2)
ax.set_title("a  Transfers follow votes", fontsize=8)
fs.hgrid(ax)
# (b) 2026 votes and 2025 transfers, net of fixed effects (binned scatter)
ax = axs[1]
B = np.array(E["binned"])
ax.scatter(100 * B[:, 0], B[:, 1], s=16, color=fs.MUSTARD, edgecolor=fs.INK, lw=0.4, zorder=3,
           label="bins of 5% of deputy-municipality pairs")
bb = E["return_main"]["pixpc"]
xs = np.linspace(100 * B[:, 0].min(), 100 * B[:, 0].max(), 10)
ax.plot(xs, bb[0] * xs / 100, color=fs.INK, lw=1.3, label=f"slope {bb[0]:.1f} points per R$ 100 (s.e. {bb[1]:.1f})")
ax.axhline(0, color=fs.AXIS, lw=0.7);
ax.axvline(0, color=fs.AXIS, lw=0.7)
ax.set_xlabel("2025 transfers per inhabitant, residual (R$)", fontsize=7)
ax.set_ylabel("2026 vote share, residual\n(percentage points)", fontsize=7)
ax.legend(fontsize=5.8, loc="upper left")
ax.set_title("b  Transfers and 2026 votes", fontsize=8)
fs.hgrid(ax)
fig.savefig(os.path.join(FIG, "figS6_electoral.png"));
fig.savefig(os.path.join(FIG, "figS6_electoral.pdf"))
print("figS6 done")
