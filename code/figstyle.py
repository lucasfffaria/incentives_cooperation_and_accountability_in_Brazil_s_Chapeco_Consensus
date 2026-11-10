# -*- coding: utf-8 -*-
"""Shared style of the figures drawn by run_all.sh (figs/): colours, fonts and the sequential and diverging colour
maps used by the fig_*.py scripts."""
import matplotlib as mpl
import matplotlib.pyplot as plt
from matplotlib.colors import LinearSegmentedColormap

# ink and structure
INK, INK2, MUTED = "#0b0b0d", "#45464b", "#7c7d82"
GRID, AXIS, SURFACE = "#e4e2dc", "#bdbcb4", "#ffffff"
# categorical slots (fixed order) and their names
CHARCOAL, MUSTARD, GREY, SUN, CREAM = "#1e1f22", "#c29c00", "#8a8b90", "#ffd34d", "#f2efe8"
CAT = [INK, MUSTARD, GREY, SUN, CREAM]
LIGHTGREY, PALE, DARKGOLD = "#c9c9cc", "#fff1bf", "#7a6300"
NEUTRAL = CREAM
OTHER = CREAM
# backwards-compatible names used by older scripts (mapped onto the yellow-black palette)
BLUE, ORANGE, AQUA, YELLOW, MAGENTA, GREEN, VIOLET, RED = (INK, MUSTARD, GREY, SUN, LIGHTGREY, CHARCOAL, GREY,
                                                            DARKGOLD)
# party -> colour (the four largest municipal parties and "other"; validated on all pairs)
PARTY_COLOR = {"PL": MUSTARD, "MDB": CHARCOAL, "PP": SUN, "PSD": GREY, "PT": LIGHTGREY, "NOVO": LIGHTGREY,
               "PSDB": LIGHTGREY, "UNIÃO": LIGHTGREY, "CIDADANIA": LIGHTGREY, "REPUBLICANOS": LIGHTGREY,
               "PODEMOS": LIGHTGREY, "OTHER": CREAM}
# display names (acronyms for PL, MDB, PP, PSD, PSDB, PT; names otherwise)
PARTY_LABEL = {"NOVO": "Novo", "UNIÃO": "União", "CIDADANIA": "Cidadania", "REPUBLICANOS": "Republicanos",
               "PODEMOS": "Podemos", "OTHER": "Other"}
EDGE = dict(edgecolor=INK, linewidth=0.5)          # dark edge for light fills


def plabel(p):
    return PARTY_LABEL.get(p, p)


# sequential: cream -> yellow -> mustard -> dark gold -> black (lightness falls monotonically)
SEQ = ["#fbf7ec", "#fff1bf", "#ffe38a", "#ffd34d", "#e8b800", "#c29c00", "#957800", "#665300", "#3b3108",
       "#0b0b0d"]
CMAP_SEQ = LinearSegmentedColormap.from_list("seq_yk", SEQ)
# diverging: negative arm grey -> black, positive arm yellow -> dark gold, cream midpoint, four steps per arm
DIV = ["#35363b", "#5f6065", "#9a9ba0", "#cfcfd2", CREAM, "#f6d566", "#d9ad00", "#a07f00", "#5e4b00"]   # L symmetric
CMAP_DIV = LinearSegmentedColormap.from_list("div_ky", DIV)
SEQ_BLUE = SEQ      # backwards-compatible name


def setup():
    mpl.rcParams.update({
        "font.family": "DejaVu Sans", "font.size": 8.5, "axes.titlesize": 9.5, "axes.titleweight": "bold",
        "axes.labelsize": 8.5, "xtick.labelsize": 7.5, "ytick.labelsize": 7.5, "legend.fontsize": 7.5,
        "axes.edgecolor": AXIS, "axes.linewidth": 0.8, "axes.labelcolor": INK2, "text.color": INK,
        "xtick.color": MUTED, "ytick.color": MUTED, "xtick.major.width": 0.6, "ytick.major.width": 0.6,
        "xtick.major.size": 2.5, "ytick.major.size": 2.5, "axes.grid": False, "grid.color": GRID,
        "grid.linewidth": 0.6, "grid.linestyle": "-", "axes.spines.top": False, "axes.spines.right": False,
        "legend.frameon": False, "figure.dpi": 150, "savefig.dpi": 400, "savefig.bbox": "tight",
        "savefig.pad_inches": 0.05, "figure.facecolor": SURFACE, "axes.facecolor": SURFACE,
        "lines.linewidth": 1.6, "lines.solid_capstyle": "round", "patch.linewidth": 0,
        "axes.titlelocation": "left", "axes.titlepad": 6,
        "axes.prop_cycle": mpl.cycler(color=[INK, MUSTARD, GREY, CHARCOAL]),
    })


def panel_label(ax, s, x=-0.02, y=1.02):
    ax.text(x, y, s, transform=ax.transAxes, fontsize=10, fontweight="bold", color=INK, ha="right", va="bottom")


def hgrid(ax):
    ax.yaxis.grid(True, color=GRID, linewidth=0.6)
    ax.set_axisbelow(True)


def vgrid(ax):
    ax.xaxis.grid(True, color=GRID, linewidth=0.6)
    ax.set_axisbelow(True)
