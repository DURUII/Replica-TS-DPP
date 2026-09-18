"""Measure the levels of Fig. 3(a), Fig. 4(a), every Fig. 5 panel and Fig. 6 from paper.pdf.

    python scripts/measure_fig_levels.py

The paper embeds each panel as a 4500x3300 RGB image. This rasterises those panels out of
the PDF with poppler's pdfimages, calibrates pixel rows/columns against the printed axis
ticks, and reads off each curve. It writes results/paper_levels.csv (Fig. 3/4),
results/paper_fig5_levels.csv (Fig. 5) and results/paper_fig6_levels.csv (Fig. 6), which
code/README.md cites, so the numbers survive the session that first obtained them.

Reading a curve, column by column:

  * Pixels that are exactly the matplotlib tab10 colour of a curve form its mask. The
    legend rectangle is punched out first because it prints samples of every colour.
  * A column through a data marker spans the whole marker, so a plain mean or median over
    the column's pixels reads the marker's edge, not the data point -- badly wrong where
    the curve is steep. Markers are therefore found explicitly, by eroding the mask with a
    square (half-width ERODE_HALF) that fits inside a marker but not inside a line. Where a
    marker core sits at the column we report its bounding-box centre, which is where
    matplotlib places the data point for every marker shape used here (circle, diamond,
    triangle). Otherwise we report the centre of the column's longest run of mask pixels,
    which lies on the polyline itself.
  * Runs separated by a few rows are merged (RUN_GAP): at a sharp vertex the two legs meet
    through a couple of rows of antialiased pixels that need not match the colour exactly.

A plateau is the median over columns sampled every 0.5 episodes across the last 10 episodes
(40-50 for Fig. 3/4, whose x-axis ends at 50; 90-100 for Fig. 5 and Fig. 6, whose axes end
at 100).

Fig. 6 is a different plot type and needs one extra idea. It plots the *time-averaged*
regret, so its first sample is the running mean's first term, not a plateau, and the
run-centre rule above cannot read it: between episode 1 and episode 2 these curves fall
hundreds of units, so the run through a column at episode 1 is the near-vertical first
segment and its centre is nowhere near the data point. Every Fig. 6 curve is monotone
decreasing from its maximum at the first sample, so the stroke's *topmost* row is that
first vertex; the reading adds half the stroke width for a solid line and nothing for a
dashed one, because the near-vertical first segment makes the solid cap reach linewidth/2
above the data point while the dashed line's butt dash cap stops on it. Those two offsets
were measured, not assumed: rasterising a polyline on axes carrying this panel's own
xlim/ylim/linewidth in matplotlib and reading the topmost tab10 pixel back gives
`topmost = y1 - 7.5` for the solid cap and `topmost = y1` for the dashed one at
linewidth 15. Fig. 6's ordinate is checked to be linear before it is calibrated as one.

Requires pdfimages (poppler), numpy and Pillow. Every input is checked up front and a
missing one aborts: a wrong or silently approximated level is worse than no level.
"""
import csv
import os
import shutil
import subprocess
import sys
import tempfile

import numpy as np
from PIL import Image

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, ".."))
PDF = os.path.join(ROOT, "paper.pdf")
RESULTS = os.path.join(ROOT, "code", "results")

PAGE_FIRST, PAGE_LAST = 6, 7     # Fig. 3 and Fig. 4 on page 6, Fig. 5 on page 7
N_IMAGES = 32                    # 16 RGB panels + 16 alpha masks over the two pages

# exact matplotlib tab10, the colours the panels were drawn with
COLORS = {
    "Lyapunov": (214, 39, 40),
    "Whittle": (44, 160, 44),
    "Belief-DPP": (255, 127, 14),     # the oracle, Fig. 3/4 only
    "TS-DPP": (31, 119, 180),
    # Fig. 6 only. Its legend labels both the dashed curve and the solid blue one
    # "L=20, V=0.5", which cannot be right -- the paper's text separates the two
    # ("the time-averaged regret of the TS-DPP algorithm converges to zero faster than
    # the upper bound we established"), so the one curve that does not decay to zero,
    # the dashed purple, is the Theorem 2 upper bound and the four solid curves are
    # TS-DPP at V in {0.5, 1, 5, 10}.
    "Bound": (148, 103, 189),
    "V=0.5": (31, 119, 180),
    "V=1": (255, 127, 14),
    "V=5": (214, 39, 40),
    "V=10": (44, 160, 44),
}
ORACLE = "Belief-DPP"

# Page 6: image 0 is Fig. 3(a), image 8 is Fig. 4(a); the odd indices are alpha masks.
# Tick labels are what the panels print; tick positions come from the image itself.
FIG34_PANELS = [
    dict(figure=3, panel="a", N=4, L=20, V=0.2, idx=0, x_last=50,
         ylabels=[78.0, 76.0, 74.0, 72.0, 70.0, 68.0, 66.0],
         curves=["Lyapunov", "Whittle", "Belief-DPP", "TS-DPP"]),
    dict(figure=4, panel="a", N=8, L=20, V=0.2, idx=8, x_last=50,
         ylabels=[102.5, 100.0, 97.5, 95.0, 92.5, 90.0, 87.5],
         curves=["Lyapunov", "Whittle", "Belief-DPP", "TS-DPP"]),
]
FIG34_LEGEND = (113, 1052, 2445, 4382)      # row0, row1, col0, col1

# Page 7: Fig. 5 is a single row of four panels. Left-to-right order (a)-(d) was checked
# against the page: the four sub-captions are centred at x = 110.7/239.8/368.8/497.8 pt and
# the four panels at x = 110.9/239.8/368.7/497.6 pt, so image index 16+k*2 is panel letter
# a+k. No oracle in this figure -- it plots TS-DPP, Lyapunov and Whittle only.
FIG5_PANELS = [
    dict(panel="a", V=0.04, idx=16, ylabels=[200.0, 175.0, 150.0, 125.0, 100.0, 75.0]),
    dict(panel="b", V=0.06, idx=18, ylabels=[180.0, 160.0, 140.0, 120.0, 100.0, 80.0, 60.0]),
    dict(panel="c", V=0.08, idx=20, ylabels=[180.0, 160.0, 140.0, 120.0, 100.0, 80.0, 60.0]),
    dict(panel="d", V=0.10, idx=22, ylabels=[160.0, 140.0, 120.0, 100.0, 80.0, 60.0]),
]
FIG5_N, FIG5_L = 3, 20
FIG5_LEGEND = (1962, 2687, 3106, 4383)
FIG5_CURVES = ["TS-DPP", "Lyapunov", "Whittle"]

# Fig. 6 is page 7's single remaining RGB panel. Page 7 carries eight of them, at global
# indices 16, 18 .. 30; Fig. 5 (a)-(d) are the first four, and dumping index 24 shows the
# one panel titled "Time-averaged Regret Plot" with its five-entry legend, so Fig. 6 is
# index 24 and Fig. 7's three panels are 26, 28, 30.
FIG6_IDX = 24
FIG6_LEGEND = (330, 1320, 2800, 3450)   # row0, row1, col0, col1; holds all five swatches
FIG6_YLABELS = [4000.0, 3000.0, 2000.0, 1000.0, 0.0]    # tick positions come from the image
FIG6_X_LAST = 100
FIG6_L = 20
FIG6_CURVES = ["Bound", "V=0.5", "V=1", "V=5", "V=10"]
FIG6_DASHED = {"Bound"}     # butt dash cap: its stroke tops out on the data point

EP_FIG34, EP_FIG5, EP_FIG6 = (40.0, 50.0), (90.0, 100.0), (90.0, 100.0)  # tail windows
EP_STEP = 0.5
ERODE_HALF = 22        # fits a data marker's inscribed square, not a line's
RUN_GAP = 10           # rows; bridges the antialiased gap at a sharp vertex
MARKER_WIN = 0.4       # episodes either side of a column searched for a marker core
DARK = 80              # a spine / tick pixel is darker than this on every channel
TICK_COLS = 30         # width of the strip beside a spine scanned for tick marks


def extract(outdir):
    """Rasterise pages 6-7; return the per-index path list."""
    if shutil.which("pdfimages") is None:
        sys.exit("pdfimages not found on PATH (install poppler)")
    prefix = os.path.join(outdir, "p")
    subprocess.run(["pdfimages", "-png", "-f", str(PAGE_FIRST), "-l", str(PAGE_LAST),
                    PDF, prefix], check=True)
    paths = [os.path.join(outdir, "p-%03d.png" % i) for i in range(N_IMAGES)]
    missing = [p for p in paths if not os.path.exists(p)]
    if missing:
        sys.exit("pdfimages produced %d images, expected %d; first missing %s"
                 % (N_IMAGES - len(missing), N_IMAGES, missing[0]))
    return paths


def load(path):
    if not os.path.exists(path):
        sys.exit("expected image %s was not extracted from %s" % (path, PDF))
    im = Image.open(path)
    if im.mode != "RGB" or im.size != (4500, 3300):
        sys.exit("image %s is %s %s, expected RGB (4500, 3300)" % (path, im.mode, im.size))
    return np.asarray(im).astype(np.int16)


def _groups(idx, tol=3):
    out = []
    for i in idx:
        if out and i - out[-1][-1] <= tol:
            out[-1].append(i)
        else:
            out.append([i])
    return [float(np.mean(g)) for g in out]


def frame_and_ticks(arr):
    """Spine rows/cols and tick rows/cols, all found in the image rather than assumed."""
    dark = arr.max(axis=2) < DARK
    rows = _groups(np.where(dark.sum(axis=1) > 2000)[0])
    cols = _groups(np.where(dark.sum(axis=0) > 1500)[0])
    if len(rows) < 2 or len(cols) < 2:
        sys.exit("could not find the axes frame (rows=%s cols=%s)" % (rows, cols))
    top, bottom = rows[0], rows[-1]
    left, right = cols[0], cols[-1]
    yticks = _groups(np.where(dark[:, int(left) - TICK_COLS:int(left) - 2].sum(axis=1) > 10)[0])
    xticks = _groups(np.where(dark[int(bottom) + 6:int(bottom) + 36, :].sum(axis=0) > 10)[0])
    # the tick-label text sits outside the axes and would otherwise register as ticks
    xticks = [c for c in xticks if left <= c <= right]
    return dict(top=top, bottom=bottom, yticks=yticks, xticks=xticks)


def square_erode(mask, s):
    """True where a (2s+1)-square fits inside mask, via 2-D prefix sums."""
    h, w = mask.shape
    c = np.zeros((h + 1, w + 1), np.int32)
    c[1:, 1:] = mask.astype(np.int32).cumsum(0).cumsum(1)
    ii, jj = np.arange(s, h - s), np.arange(s, w - s)
    inner = (c[ii + s + 1][:, jj + s + 1] - c[ii - s][:, jj + s + 1]
             - c[ii + s + 1][:, jj - s] + c[ii - s][:, jj - s])
    out = np.zeros((h, w), bool)
    out[s:h - s, s:w - s] = inner == (2 * s + 1) ** 2
    return out


def _runs(rows):
    out = []
    for r in rows:
        if out and r - out[-1][-1] <= RUN_GAP:
            out[-1].append(r)
        else:
            out.append([r])
    return out


def curve_level(mask, eroded, col, slope, inter, px_per_ep):
    """The curve's y at column `col`, in data units."""
    lo, hi = int(col - MARKER_WIN * px_per_ep), int(col + MARKER_WIN * px_per_ep)
    ys, _ = np.where(eroded[:, max(lo, 0):hi + 1])
    if ys.size:
        return slope * (ys.min() + ys.max()) / 2.0 + inter
    rows = np.where(mask[:, col])[0]
    if rows.size == 0:
        return float("nan")
    g = max(_runs(rows), key=len)
    return slope * (g[0] + g[-1]) / 2.0 + inter


def panel_setup(arr, legend, ylabels, x_last, curves):
    """Calibrate one panel and return {curve: (mask, eroded, level)}."""
    fr = frame_and_ticks(arr)
    if len(fr["yticks"]) != len(ylabels):
        sys.exit("panel at image index has %d y ticks but %d labels were given"
                 % (len(fr["yticks"]), len(ylabels)))
    slope, inter = np.polyfit(fr["yticks"], ylabels, 1)
    x0, xend = fr["xticks"][0], fr["xticks"][-1]
    px_per_ep = (xend - x0) / x_last
    out = {}
    for name in curves:
        m = np.all(arr == np.array(COLORS[name], dtype=np.int16), axis=2)
        m[legend[0]:legend[1] + 1, legend[2]:legend[3] + 1] = False
        out[name] = (m, square_erode(m, ERODE_HALF), slope, inter, px_per_ep)
    return dict(levels=out, x0=x0, xend=xend, x_last=x_last, slope=slope, inter=inter,
                top=fr["top"], bottom=fr["bottom"], ylabels=ylabels)


def column_of(setup, ep):
    return int(round(setup["x0"] + (ep / setup["x_last"]) * (setup["xend"] - setup["x0"])))


def episode_of(setup, col):
    return (col - setup["x0"]) / (setup["xend"] - setup["x0"]) * setup["x_last"]


def check_linear(yticks):
    """Abort unless the printed y ticks are evenly spaced, i.e. the ordinate is linear."""
    d = np.diff(yticks)
    if d.size == 0 or np.ptp(d) > 0.05 * abs(float(np.mean(d))):
        sys.exit("y ticks %s are not evenly spaced: the ordinate is logarithmic or "
                 "otherwise nonlinear and calibrating it as linear would be wrong"
                 % ([round(t, 1) for t in yticks],))


def legend_linewidths(arr, legend, curves):
    """Stroke width per curve, read off its legend swatch.

    A legend swatch is a horizontal sample of the curve's own Line2D, so its height is
    that line's linewidth. Reading it also proves the legend rectangle was found: a
    missing swatch means the rectangle is wrong and the swatches would be read as data.
    """
    out = {}
    for name in curves:
        m = np.all(arr == np.array(COLORS[name], dtype=np.int16), axis=2)
        ys, _ = np.where(m[legend[0]:legend[1] + 1, legend[2]:legend[3] + 1])
        if ys.size == 0:
            sys.exit("no %s pixels inside the legend rectangle %s: the legend was not "
                     "found, so its swatches would be read as curve data" % (name, legend))
        out[name] = int(ys.max() - ys.min() + 1)
    if len(set(out.values())) != 1:
        sys.exit("legend swatches have unequal heights %s, so at least one of them is "
                 "not a plain line sample" % out)
    return out


def first_point_level(name, mask, dashed, linewidth, slope, inter):
    """The curve's value at episode 1, i.e. at its first data point.

    Every Fig. 6 curve decays from its maximum at the first sample, so the stroke's
    topmost row is that vertex. The stroke reaches linewidth/2 above the vertex for a
    solid line and not at all for a dashed one; see the module docstring for how those
    two offsets were measured. The row of the topmost pixel is taken as is, in the same
    pixel-row convention `curve_level` uses.
    """
    rows = np.where(mask.any(axis=1))[0]
    if rows.size == 0:
        sys.exit("no %s pixels found in the Fig. 6 panel" % name)
    return slope * (float(rows.min()) + (0.0 if dashed else linewidth / 2.0)) + inter


def plateau(setup, name, window):
    m, er, slope, inter, px_per_ep = setup["levels"][name]
    vals = []
    for ep in np.arange(window[0], window[1] + EP_STEP / 2, EP_STEP):
        v = curve_level(m, er, column_of(setup, ep), slope, inter, px_per_ep)
        if not np.isnan(v):
            vals.append(v)
    if not vals:
        sys.exit("no %s pixels found in the panel" % name)
    return float(np.median(vals))


def main():
    if not os.path.exists(PDF):
        sys.exit("paper.pdf not found at %s" % PDF)

    tmp = tempfile.mkdtemp(prefix="figlevels-")
    try:
        paths = extract(tmp)

        # ---- Fig. 3 and Fig. 4 -------------------------------------------------
        rows, limits, oracles = [], [], {}
        for p in FIG34_PANELS:
            st = panel_setup(load(paths[p["idx"]]), FIG34_LEGEND, p["ylabels"],
                             p["x_last"], p["curves"])
            lv = {n: plateau(st, n, EP_FIG34) for n in p["curves"]}
            oracles[p["N"]] = lv[ORACLE]
            limits.append((p, st))
            for n in p["curves"]:
                rows.append(dict(figure=p["figure"], panel=p["panel"], N=p["N"], L=p["L"],
                                 V=p["V"], curve=n, plateau=round(lv[n], 2),
                                 gap_vs_oracle=round(lv[n] - lv[ORACLE], 3)))

        os.makedirs(RESULTS, exist_ok=True)
        out34 = os.path.join(RESULTS, "paper_levels.csv")
        with open(out34, "w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=["figure", "panel", "N", "L", "V", "curve",
                                               "plateau", "gap_vs_oracle"])
            w.writeheader()
            w.writerows(rows)

        for p, st in limits:
            print("Fig. %d(%s)  N=%d L=%d V=%s   y-axis %.2f .. %.2f"
                  % (p["figure"], p["panel"], p["N"], p["L"], p["V"],
                     st["slope"] * st["bottom"] + st["inter"],
                     st["slope"] * st["top"] + st["inter"]))
            print("  %-12s %8s %8s" % ("curve", "plateau", "gap"))
            for r in rows:
                if r["figure"] == p["figure"]:
                    print("  %-12s %8.2f %+8.3f" % (r["curve"], r["plateau"], r["gap_vs_oracle"]))
            print()
        print("N=8/N=4 oracle ratio: %.4f" % (oracles[8] / oracles[4]))

        # ---- Fig. 5 ------------------------------------------------------------
        print()
        fig5_rows = []
        for p in FIG5_PANELS:
            st = panel_setup(load(paths[p["idx"]]), FIG5_LEGEND, p["ylabels"], 100,
                             FIG5_CURVES)
            cols = np.concatenate([st["levels"][n][0].any(axis=0).nonzero()[0]
                                   for n in FIG5_CURVES])
            print("Fig. 5(%s)  N=%d L=%d V=%s   y-axis %.2f .. %.2f   curves span episodes "
                  "%.1f .. %.1f"
                  % (p["panel"], FIG5_N, FIG5_L, p["V"],
                     st["slope"] * st["bottom"] + st["inter"],
                     st["slope"] * st["top"] + st["inter"],
                     (cols.min() - st["x0"]) / (st["xend"] - st["x0"]) * st["x_last"],
                     (cols.max() - st["x0"]) / (st["xend"] - st["x0"]) * st["x_last"]))
            print("  %-10s %7s %7s %8s %8s" % ("curve", "ep1", "ep5", "plateau", "ep1/plat"))
            for n in FIG5_CURVES:
                m, er, slope, inter, px_per_ep = st["levels"][n]
                lvl = lambda ep: curve_level(m, er, column_of(st, ep), slope, inter,
                                             px_per_ep)
                ep1, ep5 = lvl(1.0), lvl(5.0)
                plat = plateau(st, n, EP_FIG5)
                fig5_rows.append(dict(panel=p["panel"], N=FIG5_N, L=FIG5_L, V=p["V"],
                                      curve=n, ep1=round(ep1, 2), ep5=round(ep5, 2),
                                      plateau=round(plat, 2),
                                      ep1_over_plateau=round(ep1 / plat, 3)))
                print("  %-10s %7.2f %7.2f %8.2f %8.3f" % (n, ep1, ep5, plat, ep1 / plat))
            print()

        out5 = os.path.join(RESULTS, "paper_fig5_levels.csv")
        with open(out5, "w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=["panel", "N", "L", "V", "curve", "ep1", "ep5",
                                               "plateau", "ep1_over_plateau"])
            w.writeheader()
            w.writerows(fig5_rows)

        # ---- Fig. 6 ------------------------------------------------------------
        print()
        arr6 = load(paths[FIG6_IDX])
        check_linear(frame_and_ticks(arr6)["yticks"])
        lw6 = legend_linewidths(arr6, FIG6_LEGEND, FIG6_CURVES)
        st6 = panel_setup(arr6, FIG6_LEGEND, FIG6_YLABELS, FIG6_X_LAST, FIG6_CURVES)
        fig6_rows = []
        print("Fig. 6   L=%d   y-axis %.1f .. %.1f (linear, %d ticks)   stroke width %d px"
              % (FIG6_L, st6["slope"] * st6["bottom"] + st6["inter"],
                 st6["slope"] * st6["top"] + st6["inter"], len(FIG6_YLABELS),
                 lw6[FIG6_CURVES[0]]))
        print("  %-7s %7s %8s %8s %8s %9s"
              % ("curve", "top_ep", "ep1", "ep10", "plateau", "ep1/plat"))
        for n in FIG6_CURVES:
            m, er, slope, inter, px_per_ep = st6["levels"][n]
            lvl = lambda ep: curve_level(m, er, column_of(st6, ep), slope, inter, px_per_ep)
            # the stroke's topmost row must be at the first sample, or it is not the
            # episode-1 value this reading claims to be
            ys, xs = np.where(m)
            top_ep = float(np.mean([episode_of(st6, c) for c in xs[ys == ys.min()]]))
            if not 0.5 <= top_ep <= 3.0:
                sys.exit("Fig. 6 curve %s tops out at episode %.1f, not at episode 1: "
                         "reading that row as the episode-1 value would report a "
                         "different sample" % (n, top_ep))
            ep1 = first_point_level(n, m, n in FIG6_DASHED, lw6[n], slope, inter)
            ep10, plat = lvl(10.0), plateau(st6, n, EP_FIG6)
            fig6_rows.append(dict(figure=6, panel="", L=FIG6_L, curve=n,
                                  ep1=round(ep1, 2), ep10=round(ep10, 2),
                                  plateau=round(plat, 2),
                                  ep1_over_plateau=round(ep1 / plat, 3)))
            print("  %-7s %7.2f %8.2f %8.2f %8.2f %9.3f"
                  % (n, top_ep, ep1, ep10, plat, ep1 / plat))
        print()

        out6 = os.path.join(RESULTS, "paper_fig6_levels.csv")
        with open(out6, "w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=["figure", "panel", "L", "curve", "ep1", "ep10",
                                               "plateau", "ep1_over_plateau"])
            w.writeheader()
            w.writerows(fig6_rows)

        print("wrote %s" % out34)
        print("wrote %s" % out5)
        print("wrote %s" % out6)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


if __name__ == "__main__":
    main()
