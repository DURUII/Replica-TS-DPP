"""Draw figs/*.png from results/*.csv. Nothing here simulates.

    python draw.py            # all five figures
    python draw.py 3 4        # a subset

Run `python run.py` first.

The simulation settings -- which cells, which `V`, how many episodes -- are imported from
run.py rather than repeated here, so a panel cannot silently filter on a value that nothing
simulated. What lives here is the drawing choice: `HORIZON` is how much of the stored
horizon a paper panel shows.
"""
import csv
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import matplotlib.pyplot as plt

from plot import style
from run import CELLS, FIG5_V, FIG5_L, FIG7_THETA, V_LIST

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
RESULTS = os.path.join(ROOT, "results")
FIGS = os.path.join(ROOT, "figs")
HORIZON = 50                            # episodes drawn for Fig. 3 and Fig. 4
X_TICKS = [0, 10, 20, 30, 40, 50]       # the paper's synthetic axes run 0..50, m = 50


def read(name):
    with open(os.path.join(RESULTS, name)) as fh:
        return list(csv.DictReader(fh))


def save(fig, name):
    os.makedirs(FIGS, exist_ok=True)
    path = os.path.join(FIGS, name)
    fig.savefig(path)
    plt.close(fig)
    print(f"wrote {path}")


def episodic(n, rows, name):
    spec = style.PANEL_ROW
    style.apply(spec)
    fig, axes = plt.subplots(1, 4, figsize=spec["figsize"])
    for k, (ax, (L, V)) in enumerate(zip(axes, CELLS)):
        handles = []
        for p in style.LEGEND_ORDER:
            sel = [r for r in rows
                   if int(r["N"]) == n and float(r["L"]) == L
                   and float(r["V"]) == V and r["policy"] == p
                   and int(r["episode"]) <= HORIZON]
            sel.sort(key=lambda r: int(r["episode"]))
            handles.append(style.plot_policy(
                ax, p, [int(r["episode"]) for r in sel], [float(r["penalty"]) for r in sel]))
        style.label_axes(ax)
        ax.set_xlim(-2, 52)
        ax.set_xticks(X_TICKS)
        style.legend_in_paper_order(ax, handles)
        style.subcaption(ax, f"({'abcd'[k]})  $L = {L}$, $V = {V}$", spec)
    fig.tight_layout(rect=[0, 0.10, 1, 1])
    save(fig, name)


def realworld(rows, name):
    """Fig. 5: the real-world setting, four `V` panels, three policies, no oracle."""
    spec = style.PANEL_ROW
    style.apply(spec)
    fig, axes = plt.subplots(1, 4, figsize=spec["figsize"])
    for k, (ax, V) in enumerate(zip(axes, FIG5_V)):
        handles = []
        for p in style.FIG5_ORDER:
            sel = sorted([r for r in rows
                          if float(r["V"]) == V and r["policy"] == p],
                         key=lambda r: int(r["episode"]))
            handles.append(style.plot_policy(
                ax, p, [int(r["episode"]) for r in sel],
                [float(r["penalty"]) for r in sel]))
        style.label_axes(ax)
        ax.set_xlim(-4, 104)
        ax.set_xticks([0, 20, 40, 60, 80, 100])
        style.legend_in_paper_order(ax, handles, loc="lower right", order=style.FIG5_ORDER)
        style.subcaption(ax, f"({'abcd'[k]})  $L = {FIG5_L}$, $V = {V:g}$", spec)
    fig.tight_layout(rect=[0, 0.10, 1, 1])
    save(fig, name)


def regret(rows, name):
    spec = style.SINGLE
    style.apply(spec)
    fig, ax = plt.subplots(figsize=spec["figsize"])
    handles = []
    for c, V in zip(style.V_COLOR, V_LIST):
        sel = sorted([r for r in rows if float(r["V"]) == V],
                     key=lambda r: int(r["episode"]))
        h, = ax.plot([int(r["episode"]) for r in sel],
                     [float(r["time_averaged_regret"]) for r in sel],
                     lw=1.0, color=c, label=f"L=20, V={V:g}")
        handles.append(h)
    first = sorted([r for r in rows if float(r["V"]) == V_LIST[0]],
                   key=lambda r: int(r["episode"]))
    bound, = ax.plot([int(r["episode"]) for r in first],
                     [float(r["upper_bound"]) for r in first],
                     "--", color="tab:purple", lw=1.0, label=f"L=20, V={V_LIST[0]:g}")
    style.label_axes(ax, ylabel="Time-averaged Regret")
    ax.set_title("Time-averaged Regret Plot")
    ax.set_xticks([0, 20, 40, 60, 80, 100])
    ax.set_xlim(-4, 104)
    top = max(float(r["upper_bound"]) for r in first)
    ax.set_ylim(0, top * 1.06)          # keep the episode-1 anchor off the frame
    ax.legend([bound] + handles, [h.get_label() for h in [bound] + handles],
              loc="upper right", framealpha=1.0)
    fig.tight_layout()
    save(fig, name)


def estimates(rows, name):
    spec = style.TRIPLE
    style.apply(spec)
    fig, axes = plt.subplots(1, 3, figsize=spec["figsize"])
    thetas = FIG7_THETA
    for k, (ax, ts) in enumerate(zip(axes, thetas)):
        sel = sorted([r for r in rows if float(r["theta"]) == ts],
                     key=lambda r: int(r["episode"]))
        e = [int(r["episode"]) for r in sel]
        ax.fill_between(e, [float(r["ci_low"]) for r in sel],
                        [float(r["ci_high"]) for r in sel],
                        color="b", alpha=0.20, lw=0)
        ax.plot(e, [float(r["mean"]) for r in sel], "-+", color="b", ms=4.5, lw=0.9)
        ax.axhline(ts, color="tab:red", lw=1.2)
        ax.set_title("Parameter Estimate with 95% CI")
        style.label_axes(ax, ylabel="Episodic Estimation")
        ax.set_xticks([0, 20, 40, 60, 80, 100])
        ax.set_xlim(-4, 104)
        # The paper frames the estimate, not the credible interval: its first panel spans
        # about 0.15 to 0.65, so the wide prior band at episode 0 runs off the bottom.
        m = [float(r["mean"]) for r in sel]
        ax.set_ylim(max(0.0, min(m) - 0.10), min(1.0, max(m) + 0.10))
        style.subcaption(ax, rf"({'abc'[k]})  $\theta = {ts}$", spec)
    fig.tight_layout(rect=[0, 0.09, 1, 1])
    save(fig, name)


if __name__ == "__main__":
    want = sys.argv[1:] or ["3", "4", "5", "6", "7"]
    if "3" in want or "4" in want:
        curves = read("penalty_curves.csv")
        if "3" in want:
            episodic(4, curves, "fig3.png")
        if "4" in want:
            episodic(8, curves, "fig4.png")
    if "5" in want:
        realworld(read("realworld_curves.csv"), "fig5.png")
    if "6" in want:
        regret(read("regret.csv"), "fig6.png")
    if "7" in want:
        estimates(read("estimates.csv"), "fig7.png")
