# -*- coding: utf-8 -*-
"""Figure 1 (real data): counties, mayors' parties and the real status-quo amendments per inhabitant;
Supplementary map of losers. Writes figs/fig1_sc.(png|pdf) and out/region_numbers.json."""
import json, os
import numpy as np, pandas as pd, geopandas as gpd
import matplotlib.pyplot as plt
from matplotlib.patches import Patch
from matplotlib.colors import LogNorm
import figstyle as fs

fs.setup()
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
D, FIG, OUT = os.path.join(ROOT, "data"), os.path.join(ROOT, "figs"), os.path.join(ROOT, "out")
m = pd.read_csv(os.path.join(D, "derived", "sc_master2.csv"))
gdf = gpd.read_file(os.path.join(D, "geojs-42-mun.json"))
gdf["ibge_id"] = gdf["id"].astype(int)
gdf = gdf.merge(m, on="ibge_id", how="left").to_crs(31982)
reg_gdf = gdf.dissolve(by="health_region_2024").reset_index()
reg_gdf["rep"] = reg_gdf.geometry.representative_point()
reg_gdf["rep_x"] = reg_gdf["rep"].x
xy = gpd.GeoSeries(gpd.points_from_xy(m.longitude, m.latitude), crs=4326).to_crs(31982)
m["px"], m["py"] = xy.x.values, xy.y.values
order = reg_gdf.sort_values("rep_x").health_region_2024.tolist()
num = {r: i + 1 for i, r in enumerate(order)}
json.dump(num, open(os.path.join(OUT, "region_numbers.json"), "w"), ensure_ascii=False, indent=1)
regions = sorted(m.health_region_2024.unique())
TINTS = ["#fff1bf", "#dcdcdf", "#ffe08a", "#f4f1ea", "#bfc0c4"]      # yellow and grey tints (map colouring)
geoms = dict(zip(reg_gdf.health_region_2024, reg_gdf.geometry))
adj = {r: {s for s in regions if s != r and geoms[r].buffer(50).intersects(geoms[s])} for r in regions}
col = {}
for r in sorted(regions, key=lambda r: -len(adj[r])):
    used = {col[n] for n in adj[r] if n in col}
    col[r] = next(c for c in TINTS if c not in used)


def outline(ax, lw=1.0):
    reg_gdf.boundary.plot(ax=ax, color="white", linewidth=lw + 1.0, zorder=4)
    reg_gdf.boundary.plot(ax=ax, color=fs.INK2, linewidth=lw * 0.5, zorder=5)


def scalebar(ax, km=100):
    x0, x1 = ax.get_xlim();
    y0, y1 = ax.get_ylim()
    x, y = x0 + 0.03 * (x1 - x0), y0 + 0.05 * (y1 - y0)
    ax.plot([x, x + km * 1000], [y, y], color=fs.INK2, lw=1.2, solid_capstyle="butt")
    ax.text(x + km * 500, y + 0.02 * (y1 - y0), f"{km} km", ha="center", va="bottom", fontsize=6.5, color=fs.INK2)


fig = plt.figure(figsize=(7.2, 8.6))
gsp = fig.add_gridspec(3, 2, width_ratios=[3.0, 1.15], hspace=0.22, wspace=0.0)
# (a) counties
ax = fig.add_subplot(gsp[0, 0]);
axl = fig.add_subplot(gsp[0, 1]);
axl.set_axis_off()
gdf.plot(ax=ax, color=[col[r] for r in gdf.health_region_2024], edgecolor="white", linewidth=0.25)
outline(ax)
pol = m[m.polo]
ax.scatter(pol.px, pol.py, marker="*", s=40, color=fs.INK, edgecolor="white", linewidth=0.5, zorder=6)
for _, r in reg_gdf.iterrows():
    p = r.rep
    pp = pol[pol.health_region_2024 == r.health_region_2024].iloc[0]
    tx, ty = p.x, p.y
    if np.hypot(tx - pp.px, ty - pp.py) < 14000:
        ty -= 18000
    ax.text(tx, ty, str(num[r.health_region_2024]), fontsize=6.8, fontweight="bold", ha="center", va="center",
            color=fs.INK, zorder=7, bbox=dict(boxstyle="circle,pad=0.15", fc="white", ec="none", alpha=0.9))
ax.set_axis_off();
ax.set_aspect("equal");
scalebar(ax)
ax.set_title("a   Counties: the 17 SUS health regions", loc="left", fontsize=8.5)
lines = [f"{num[r]:>2}  {r} ({pol[pol.health_region_2024 == r].municipality.iloc[0]})" for r in order]
axl.text(0.0, 0.98, "\n".join(lines), va="top", ha="left", fontsize=5.6, color=fs.INK2, linespacing=1.32,
         transform=axl.transAxes)
axl.text(0.0, 0.02, "★ largest municipality of the county", fontsize=5.8, color=fs.INK2, transform=axl.transAxes)
# (b) mayors' parties
ax = fig.add_subplot(gsp[1, 0]);
axl = fig.add_subplot(gsp[1, 1]);
axl.set_axis_off()
MAIN = ["PL", "MDB", "PP", "PSD"]
pc = {p: (fs.PARTY_COLOR[p] if p in MAIN else fs.OTHER) for p in m.party.unique()}
gdf.plot(ax=ax, color=[pc.get(p, fs.OTHER) for p in gdf.party], edgecolor="#9a9ba0", linewidth=0.2)
outline(ax)
ax.set_axis_off();
ax.set_aspect("equal")
ax.set_title("b   Party of the mayor elected in October 2024", loc="left", fontsize=8.5)
cnt = m.party.value_counts()
handles = [Patch(facecolor=pc[p], edgecolor=fs.INK, linewidth=0.4, label=f"{fs.plabel(p)} ({cnt[p]})") for p in MAIN]
oth = [p for p in cnt.index if p not in MAIN]
handles.append(Patch(facecolor=fs.OTHER, edgecolor=fs.INK, linewidth=0.4, label="Other (" + str(int(cnt[oth].sum())) + ")\n" +
                     ", ".join(f"{fs.plabel(p)} {cnt[p]}" for p in oth)))
axl.legend(handles=handles, loc="center left", fontsize=6.4, frameon=False, handlelength=1.1)
# (c) status-quo amendments per inhabitant (real 2025 special-transfer geography scaled to the quota)
ax = fig.add_subplot(gsp[2, 0]);
axl = fig.add_subplot(gsp[2, 1]);
axl.set_axis_off()
v = gdf.x_sq_pc.values.copy()
zero = v < 1
norm = LogNorm(vmin=5, vmax=1500)
gdf[~zero].plot(ax=ax, color=fs.CMAP_SEQ(norm(np.clip(v[~zero], 5, 1500))), edgecolor="white", linewidth=0.2)
gdf[zero].plot(ax=ax, facecolor="white", edgecolor=fs.LIGHTGREY, linewidth=0.2, hatch="////")
outline(ax)
ax.set_axis_off();
ax.set_aspect("equal")
ax.set_title("c   Individual amendments today (R$ per inhabitant per year)", loc="left", fontsize=8.5)
cax = axl.inset_axes([0.05, 0.35, 0.12, 0.55])
sm = plt.cm.ScalarMappable(norm=norm, cmap=fs.CMAP_SEQ)
cb = fig.colorbar(sm, cax=cax)
cb.set_ticks([5, 10, 30, 100, 300, 1000]);
cb.set_ticklabels(["5", "10", "30", "100", "300", "1,000"])
cb.ax.tick_params(labelsize=6, length=2)
cb.outline.set_linewidth(0.4)
axl.legend(handles=[Patch(facecolor="white", hatch="////", edgecolor=fs.MUTED, label="none in the\nstatus quo")],
           loc="lower left", bbox_to_anchor=(0.0, 0.05), fontsize=6.0, frameon=False)
fig.savefig(os.path.join(FIG, "fig1_sc.png"));
fig.savefig(os.path.join(FIG, "fig1_sc.pdf"))
print("fig1 done")
