# -*- coding: utf-8 -*-
"""Supplementary figures: S1 voting power (real data), S2 calibration checks of the mayors' module,
S3 Morris screening, S4 maps of losers, S5 conde party in one world and across worlds."""
import os, json
import numpy as np, pandas as pd, geopandas as gpd
import matplotlib.pyplot as plt
import figstyle as fs
from cc2_data import Geo, PARTIES
from cc2_params import sample, PRIORS
from cc2_model import draw_random, simulate

fs.setup()
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FIG, OUT = os.path.join(ROOT, "figs"), os.path.join(ROOT, "out")
C = json.load(open(os.path.join(OUT, "real_colleges.json")))
# ---------------------------------------------------------------- S1: Banzhaf power of the largest city
bz = pd.DataFrame(C["banzhaf"]).sort_values("polo_pop_share")
fig, ax = plt.subplots(figsize=(7.0, 4.4))
yy = np.arange(len(bz))
for yi, (_, r) in zip(yy, bz.iterrows()):
    vals = [r.banzhaf_1m1v, r.polo_pop_share, r.banzhaf_dual, r.banzhaf_pop]
    ax.plot([min(vals), max(vals)], [yi, yi], color=fs.GRID, lw=1.6, zorder=1, solid_capstyle="round")
ax.scatter(bz.polo_pop_share, yy, s=34, marker="|", color=fs.INK, linewidths=1.6, zorder=4, label="population share")
ax.scatter(bz.banzhaf_1m1v, yy, s=24, color=fs.INK, marker="o", zorder=3, label="one mayor, one vote")
ax.scatter(bz.banzhaf_dual, yy, s=24, color=fs.GREY, marker="s", edgecolor=fs.INK, linewidths=0.4, zorder=3,
           label="dual majority (mayors and population)")
ax.scatter(bz.banzhaf_pop, yy, s=26, color=fs.MUSTARD, marker="D", edgecolor=fs.INK, linewidths=0.4, zorder=3,
           label="weighted by population")
ax.set_yticks(yy)
ax.set_yticklabels([f"{r.region} ({r.polo}, n = {r.n})" for _, r in bz.iterrows()], fontsize=6.7)
ax.set_xlim(-0.01, 1.03)
ax.set_xlabel("Normalized Banzhaf power of the county's largest municipality")
fs.vgrid(ax)
ax.tick_params(axis="y", length=0, labelcolor=fs.INK2)
ax.spines["left"].set_visible(False)
ax.legend(loc="lower right", fontsize=6.8, handletextpad=0.4, borderaxespad=0.2)
ax.set_title("Voting power of the largest municipality in each county's college", fontsize=9)
fig.savefig(os.path.join(FIG, "figS1_banzhaf.png"));
fig.savefig(os.path.join(FIG, "figS1_banzhaf.pdf"));
plt.close(fig)
# ---------------------------------------------------------------- S2: calibration checks (status quo, 1,000 worlds)
geo = Geo()
P, _ = sample(1000, seed=20261008)
R = draw_random(1000, geo, seed=4242)
o = simulate(P, "SQ", geo, R)
st = json.load(open(os.path.join(ROOT, "data", "derived", "data_stats.json")))["mayors"]


def tv(a, b):
    ks = set(a) | set(b)
    return 0.5 * sum(abs(a.get(k, 0) - b.get(k, 0)) for k in ks)


mom = [("Eligible incumbents who run", o["el_runs"] / o["el_elig"], [st["run_2020"], st["run_2024"]]),
       ("Runners who win", o["el_wins"] / o["el_runs"], [st["win_2020"], st["win_2024"]]),
       ("Re-elected who changed party", o["el_sw"] / o["el_wins"], [st["switch_reelected_2020"],
                                                                    st["switch_reelected_2024"]]),
       ("Open seats kept by the party", o["el_kept"] / o["el_open"], [st["open_kept_2020"], st["open_kept_2024"]]),
       ("Change in party shares (TV)", o["tv_party"], [tv(st["party_shares_2016"], st["party_shares_2020"]),
                                                       tv(st["party_shares_2020"], st["party_shares_2024"])]),
       ("Term-limited share after an election", o["el_wins"] / 3 / 295, [st["lame_duck_share_2021_24"],
                                                                          st["term_limited_share_2025_28"]])]
fig, ax = plt.subplots(figsize=(6.6, 3.0))
for i, (lab, v, obs) in enumerate(mom):
    y = len(mom) - 1 - i
    lo, md, hi = np.percentile(v, [5, 50, 95])
    ax.plot([lo, hi], [y, y], color=fs.INK, lw=1.0)
    ax.scatter(md, y, s=20, color=fs.INK, zorder=3, label="model, status quo (median, 5th-95th)" if i == 0 else None)
    ax.scatter(obs, [y + 0.18] * 2, s=24, marker="D", color=fs.MUSTARD, edgecolor=fs.INK, linewidths=0.4, zorder=3,
               label="Santa Catarina, two cycles (2016-20, 2020-24)" if i == 0 else None)
ax.set_yticks(range(len(mom)));
ax.set_yticklabels([m_[0] for m_ in mom][::-1], fontsize=7)
ax.set_xlim(0, 0.9);
ax.set_xlabel("Share")
ax.legend(fontsize=6.5, loc="lower right")
fs.vgrid(ax)
ax.set_title("Mayors' dynamics: model and data", fontsize=9)
fig.savefig(os.path.join(FIG, "figS2_calibration.png"));
fig.savefig(os.path.join(FIG, "figS2_calibration.pdf"));
plt.close(fig)
json.dump({m_[0]: dict(model=[float(x) for x in np.percentile(m_[1], [5, 50, 95])], data=[float(x) for x in m_[2]])
           for m_ in mom}, open(os.path.join(OUT, "cc2_calibration_checks.json"), "w"), indent=1)
# ---------------------------------------------------------------- S3: Morris screening
G = json.load(open(os.path.join(OUT, "cc2_gsa_R0.json")))
outs = [("dval_need", "Need-weighted value (%)"), ("coop", "Cooperation"), ("reg_share", "Regional share"),
        ("ch_leg_effort", "Legislative effort")]
fig, axs = plt.subplots(1, 4, figsize=(7.4, 3.2), gridspec_kw=dict(wspace=0.95))
for ax, (k, lab) in zip(axs, outs):
    mu = G["morris"][k]["mu_star"]
    top = sorted(mu.items(), key=lambda t: -t[1])[:10][::-1]
    ax.barh(range(len(top)), [t[1] for t in top], color=fs.MUSTARD, edgecolor=fs.INK, linewidth=0.4, height=0.6)
    ax.set_yticks(range(len(top)));
    ax.set_yticklabels([t[0] for t in top], fontsize=6.2)
    ax.set_title(lab, fontsize=7.5)
    ax.tick_params(axis="x", labelsize=6)
    fs.vgrid(ax)
fig.suptitle("Morris screening (mean absolute elementary effect, proposal as stated)", fontsize=8.5, y=1.0)
fig.savefig(os.path.join(FIG, "figS3_morris.png"));
fig.savefig(os.path.join(FIG, "figS3_morris.pdf"));
plt.close(fig)
# ---------------------------------------------------------------- S4: maps of losers
mun = np.load(os.path.join(OUT, "cc2_mun.npz"))
m = pd.read_csv(os.path.join(ROOT, "data", "derived", "sc_master2.csv"))
gdf = gpd.read_file(os.path.join(ROOT, "data", "geojs-42-mun.json"))
gdf["ibge_id"] = gdf["id"].astype(int)
gdf = gdf.merge(m, on="ibge_id", how="left").to_crs(31982)
reg = gdf.dissolve(by="health_region_2024").reset_index()
pos = {ib: i for i, ib in enumerate(m.ibge_id)}
fig, axs = plt.subplots(1, 2, figsize=(7.2, 2.9))
for ax, (d, lab) in zip(axs, (("R0", "a  Proposal as stated"), ("R16", "b  Robust variant + need-based split"))):
    ch = np.median((mun[d] - mun["SQ"]) / 12, axis=0) / m.pop2022.values
    vals = np.array([ch[pos[i]] for i in gdf.ibge_id])
    norm = plt.Normalize(-150, 150)
    gdf.plot(ax=ax, color=fs.CMAP_DIV(norm(np.clip(vals, -150, 150))), edgecolor="white", linewidth=0.2)
    reg.boundary.plot(ax=ax, color=fs.INK2, linewidth=0.5)
    ax.set_axis_off();
    ax.set_aspect("equal")
    ax.set_title(lab, fontsize=8)
sm = plt.cm.ScalarMappable(cmap=fs.CMAP_DIV, norm=plt.Normalize(-150, 150))
cax = fig.add_axes([0.92, 0.2, 0.012, 0.6])
cb = fig.colorbar(sm, cax=cax);
cb.ax.tick_params(labelsize=6);
cb.set_label("median change in value received\n(R$ per inhabitant per year)", fontsize=6.5)
fig.savefig(os.path.join(FIG, "figS4_losers.png"));
fig.savefig(os.path.join(FIG, "figS4_losers.pdf"));
plt.close(fig)
print("supplementary figures done")
