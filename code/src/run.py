"""Run the simulations and write results/*.csv. Nothing here plots.

    python run.py episodic [runs]     # Fig. 3 and Fig. 4
    python run.py realworld [runs]    # Fig. 5
    python run.py regret              # Fig. 6
    python run.py estimates           # Fig. 7
    python run.py all [runs]

Every figure in figs/ is drawn from the CSVs this writes, so draw.py never re-runs a
simulation. Re-running with a different `runs` overwrites the same files.
"""
import csv
import os
import sys

import numpy as np

from sim import model, realworld

HERE = os.path.dirname(os.path.abspath(__file__))
RESULTS = os.path.abspath(os.path.join(HERE, "..", "results"))

TAIL = 10                      # episodes averaged for the steady-state numbers
CELLS = [(20, 0.2), (30, 0.2), (20, 0.5), (30, 0.5)]
V_LIST = [0.5, 1.0, 5.0, 10.0]
FIG5_V = [0.04, 0.06, 0.08, 0.1]        # the paper's Fig. 5 sweep
FIG5_L = 20
FIG5_M = 100
FIG5_POLICIES = ("lyapunov", "tsdpp", "whittle")    # Fig. 5 draws three, no oracle
FIG7_THETA = [0.239, 0.489, 0.839]      # the paper's three, in its panel order
FIG7_L = 20
FIG7_M = 100
FIG7_V = 0.5


def write(name, header, rows):
    os.makedirs(RESULTS, exist_ok=True)
    path = os.path.join(RESULTS, name)
    with open(path, "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(header)
        w.writerows(rows)
    print(f"wrote {path}  ({len(rows)} rows)")


def episodic(runs=500, m=100):
    """Fig. 3 (N=4) and Fig. 4 (N=8): episodic penalty trends.

    The paper runs `m = 50` for the synthetic setting. We simulate to 100 and store every
    episode, so draw.py's `HORIZON` can move inside the stored 0..100 without re-simulating.
    See README, Difference 4.
    """
    curves, tails = [], []
    for n in (4, 8):
        for L, V in CELLS:
            acc = {p: [] for p in ("oracle", "tsdpp", "lyapunov", "whittle")}
            for r in range(runs):
                rng = np.random.default_rng(9000 + r)      # same draw for every policy
                theta, gamma, c = model.draw_instance(rng, n)
                for p in acc:
                    rng_p = np.random.default_rng(9000 + r)
                    pen, cost = model.simulate(theta, gamma, c, m, L, p, rng_p, V)
                    acc[p].append(pen)
                    tails.append([n, L, V, p, r,
                                  round(float(pen[-TAIL:].mean()), 6), round(cost, 6)])
            for p, arr in acc.items():
                mean = np.array(arr).mean(axis=0)
                for e, v in enumerate(mean, start=1):
                    curves.append([n, L, V, p, e, round(float(v), 6)])
            print(f"  N={n} L={L} V={V} done over {runs} runs")
    write("penalty_curves.csv", ["N", "L", "V", "policy", "episode", "penalty"], curves)
    write("penalty_tails.csv",
          ["N", "L", "V", "policy", "run", "tail_penalty", "cost"], tails)


def realworld_setting(runs=1000, m=FIG5_M, L=FIG5_L):
    """Fig. 5: N = 3, L = 20, m = 100, V in {0.04, 0.06, 0.08, 0.1}, three policies.

    Only `theta` comes from the data. The paper does not say where `gamma` or `c` go in
    the real-world setting, so they keep the synthetic setting's distributions, and each
    run draws one instance and simulates all four `V` on it so the panels stay paired.

    `carry=True`: the trace does not pause between episodes, so neither does the AoI.
    Without it the steady state is 99 instead of 156 and Fig. 5 comes out flat. See
    README, Difference 6, which also covers the run count; `diagnose.py carry` measures
    both settings side by side.
    """
    theta, stream = realworld.load()
    print(f"  {realworld.DEFAULT}: per-slot event rate "
          + " ".join(f"{t}={p:.4f}" for t, p in zip(realworld.TYPES, theta)))
    acc = {(V, p): [] for V in FIG5_V for p in FIG5_POLICIES}
    tails = []
    for r in range(runs):
        rng = np.random.default_rng(60000 + r)
        n = len(theta)
        gamma, c = rng.dirichlet(np.ones(n)), rng.uniform(0.2, 0.5, n)
        for V in FIG5_V:
            for p in FIG5_POLICIES:
                pen, cost = model.simulate(theta, gamma, c, m, L, p,
                                           np.random.default_rng(60000 + r), V,
                                           stream=stream, carry=True)
                acc[(V, p)].append(pen)
                tails.append([L, V, p, r, round(float(pen[-TAIL:].mean()), 6),
                              round(cost, 6)])
        if (r + 1) % 50 == 0:
            print(f"  {r + 1}/{runs} instances")

    curves = []
    for V in FIG5_V:
        for p in FIG5_POLICIES:
            mean = np.array(acc[(V, p)]).mean(axis=0)
            for e, v in enumerate(mean, start=1):
                curves.append([L, V, p, e, round(float(v), 6)])
    write("realworld_curves.csv",
          ["L", "V", "policy", "episode", "penalty"], curves)
    write("realworld_tails.csv",
          ["L", "V", "policy", "run", "tail_penalty", "cost"], tails)


def regret(mc=1000, m=100, L=20, n=4):
    """Fig. 6: time-averaged regret of TS-DPP against the oracle, per V."""
    acc = {V: np.zeros(m) for V in V_LIST}
    oracle = {V: np.zeros(m) for V in V_LIST}
    for r in range(mc):
        for V in V_LIST:
            rng = np.random.default_rng(40000 + r)
            theta, gamma, c = model.draw_instance(rng, n)
            oracle[V] += model.simulate(theta, gamma, c, m, L, "oracle",
                                        np.random.default_rng(40000 + r), V)[0]
            acc[V] += model.simulate(theta, gamma, c, m, L, "tsdpp",
                                     np.random.default_rng(40000 + r), V)[0]
        if (r + 1) % 200 == 0:
            print(f"  {r + 1}/{mc} Monte Carlo draws")
    for V in V_LIST:
        acc[V] /= mc
        oracle[V] /= mc

    eps = np.arange(1, m + 1)
    T = eps * L
    raw = np.sqrt(L ** 3 * T * np.log(T) + L * T) / T      # Theorem 2 / Remark 3, per slot
    rows = []
    for V in V_LIST:
        running = np.cumsum(acc[V] - oracle[V]) / eps
        bound = running[0] * raw / raw[0]                  # anchored at episode 1
        for e in range(m):
            rows.append([V, e + 1, round(float(running[e]), 8), round(float(bound[e]), 8)])
    write("regret.csv", ["V", "episode", "time_averaged_regret", "upper_bound"], rows)


def estimates(seed=7, m=FIG7_M, L=FIG7_L):
    """Fig. 7: posterior mean and 95% credible interval per episode, one realisation.

    The three `theta` are the paper's own three panels -- one large, one medium, one small,
    which is how its text describes them. The rollout is `model.posterior_path`, shared with
    `diagnose.py fig7` so that what the figure draws and what gets measured for calibration
    are the same estimator.
    """
    theta = np.array(FIG7_THETA)
    n = len(theta)
    rng = np.random.default_rng(seed)
    gamma, c = rng.dirichlet(np.ones(n)), rng.uniform(0.2, 0.5, n)
    mean, lo, hi = model.posterior_path(theta, gamma, c, m, L, rng, FIG7_V)
    rows = []
    for l in range(m + 1):
        for i in range(n):
            rows.append([theta[i], l, round(float(mean[l, i]), 6),
                         round(float(lo[l, i]), 6), round(float(hi[l, i]), 6)])
    write("estimates.csv", ["theta", "episode", "mean", "ci_low", "ci_high"], rows)


if __name__ == "__main__":
    what = sys.argv[1] if len(sys.argv) > 1 else "all"
    runs = int(sys.argv[2]) if len(sys.argv) > 2 else 500
    if what in ("episodic", "all"):
        print("episodic penalty (Fig. 3, Fig. 4)")
        episodic(runs)
    if what in ("realworld", "all"):
        print("real-world episodic penalty (Fig. 5)")
        realworld_setting(runs if len(sys.argv) > 2 else 1000)
    if what in ("regret", "all"):
        print("time-averaged regret (Fig. 6)")
        regret()
    if what in ("estimates", "all"):
        print("parameter estimates (Fig. 7)")
        estimates()
