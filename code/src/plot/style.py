"""Matplotlib style, measured off the paper's own panels (Fig. 3, Fig. 4, Fig. 5).

  markers   Lyapunov ^ (red) | Whittle D (green) | Belief-DPP oracle s (orange)
            | TS-DPP o (blue)   -- the four matplotlib default colour slots, so the
            authors plotted in the order TS-DPP, oracle, Whittle, Lyapunov and then
            reordered the legend.
  Fig. 7    blue "+" markers on a blue line, light blue 95% band, red true-value line.
  captions  "(a)  $L = 20$, $V = 0.2$" in serif italic below the axes: that is the
            IEEE subcaption, not a matplotlib title.
  no grid anywhere.
"""
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

plt.rcParams.update({
    "font.family": "sans-serif",
    "font.sans-serif": ["DejaVu Sans"],
    "mathtext.fontset": "cm",
    "axes.labelweight": "bold",
    "axes.titleweight": "bold",
    "axes.linewidth": 0.8,
    "savefig.dpi": 750,
    "savefig.bbox": "tight",
    "axes.grid": False,
})

POLICY = {
    "lyapunov": ("Lyapunov", "tab:red", "^"),
    "whittle": ("Whittle", "tab:green", "D"),
    "oracle": ("Belief-DPP (oracle)", "tab:orange", "s"),
    "tsdpp": ("TS-DPP", "tab:blue", "o"),
}
LEGEND_ORDER = ["lyapunov", "whittle", "oracle", "tsdpp"]

# Fig. 5 drops the oracle and keeps every remaining policy's marker, so it needs its own
# legend order but no marker set of its own.
FIG5_ORDER = ["lyapunov", "whittle", "tsdpp"]

# Fig. 6 colours, read off the paper's own legend: V=0.5 blue, 1 orange, 5 red, 10 green.
V_COLOR = ["tab:blue", "tab:orange", "tab:red", "tab:green"]

LW = 1.0
MS = 6.0

# per-figure sizing.  Panel aspect follows the paper: the four-panel rows are the
# widest, the single-panel regret plot the smallest, the estimate row the tallest.
PANEL_ROW = dict(figsize=(23.0, 5.5), label=15, tick=13.5, legend=11.5, caption=16)
SINGLE = dict(figsize=(4, 4), label=11.5, tick=10.5, legend=9, caption=11)
TRIPLE = dict(figsize=(10, 4), label=13, tick=12, legend=10.5, caption=14)


def apply(spec):
    plt.rcParams.update({
        "axes.labelsize": spec["label"],
        "axes.titlesize": spec["label"],
        "xtick.labelsize": spec["tick"],
        "ytick.labelsize": spec["tick"],
        "legend.fontsize": spec["legend"],
    })


def plot_policy(ax, key, x, y):
    label, color, marker = POLICY[key]
    return ax.plot(x, y, color=color, marker=marker, ms=MS, lw=LW, label=label)[0]


def label_axes(ax, xlabel="Episodes", ylabel="Episodic Penalty"):
    ax.set_xlabel(xlabel, labelpad=4)
    ax.set_ylabel(ylabel, labelpad=4)
    ax.tick_params(width=0.8, length=3.5)


def legend_in_paper_order(ax, handles, loc="upper right", order=LEGEND_ORDER):
    """The paper's legend order differs from its plotting order."""
    by_label = {h.get_label(): h for h in handles}
    head = [by_label[POLICY[k][0]] for k in order if POLICY[k][0] in by_label]
    tail = [h for h in handles if h not in head]
    ordered = head + tail
    ax.legend(ordered, [h.get_label() for h in ordered],
              loc=loc, framealpha=1.0, borderpad=0.5, handlelength=2.2)


def subcaption(ax, text, spec, y=-0.36):
    ax.text(0.5, y, text, transform=ax.transAxes, ha="center", va="top",
            fontsize=spec["caption"], family="serif")
