"""Why the baselines do not land where the paper plots them, and where Fig. 5's shape
comes from.

    python diagnose.py gaps       # paired gap of every policy against the oracle
    python diagnose.py variants   # which baseline variant reproduces the paper's ordering
    python diagnose.py whittle    # why the Whittle baseline beats both TS-DPP and the oracle
    python diagnose.py cost       # realised cost per policy against B = 0.35
    python diagnose.py carry      # the episode-boundary choice behind Fig. 5
    python diagnose.py fig7       # whether Fig. 7's shaded band is calibrated
    python diagnose.py eq14       # where Fig. 7's posterior bias comes from

`fig7` measures that the band is mis-calibrated; `eq14` locates the cause. It drives
`simulate` with a round-robin `rule` instead of a policy, so every arm is pulled on a fixed
cadence of `n` and the arm-selection layer drops out of the experiment entirely. Four
tables: (A) at that cadence Eq (14) still carries a bias that the episode boundary, not the
formula, is responsible for -- running the same call with `carry=True` moves it; (B) the
per-pull estimator has a closed form and equals `theta` exactly at every cadence, so the
formula is not the problem; (C) the size of the artifact is read straight off the final
`alpha` and `beta` of two runs on the same seed; (D) the bias does not decay as pulls
accumulate -- `bias * pulls` grows linearly, so it is a fixed offset and not a 1/count
effect that would wash out with more data. The results are in results/eq14.csv.

`variants` is the discriminating experiment. Hsu's closed form [24] is derived for a
subproblem where serving an arm resets its age to 1; here a pull sets Y := X + 1, so the
two are not isomorphic. If Hsu verbatim lands clearly ABOVE the oracle while the index
derived for this model's arm lands BELOW it, the paper ran the former.

Every number here comes out of `model.simulate`, so the diagnostics share the rollout loop,
the virtual queue and the seeding convention with run.py: the instance is drawn from one
stream and each rollout then consumes a fresh stream seeded identically. That is what pairs
the policies within a run, and what makes these CSVs comparable with run.py's.
"""
import csv
import os
import sys

import numpy as np

from run import CELLS, FIG5_L, FIG5_M, FIG5_V, FIG7_L, FIG7_M, FIG7_THETA, FIG7_V
from sim import model, realworld, whittle

HERE = os.path.dirname(os.path.abspath(__file__))
RESULTS = os.path.abspath(os.path.join(HERE, "..", "results"))

N, M, RUNS = 4, 50, 200
L, V = CELLS[0]                  # the panel every single-instance diagnostic runs on
B = model.B_DEFAULT
TAIL = 10


def _rollout(pick, seed, policy_name="plugin"):
    """One rollout with a caller-supplied selection rule.

    `policy_name` picks what the algorithm is *told*, not what it does: "oracle" hands it
    `theta*`, anything else the posterior mean. The queue runs either way.
    """
    theta, gamma, c = model.draw_instance(np.random.default_rng(seed), N)
    pen, cost = model.simulate(theta, gamma, c, M, L,
                               "oracle" if policy_name == "oracle" else "lyapunov",
                               np.random.default_rng(seed), V, rule=pick)
    return pen[-TAIL:].mean(), cost


def oracle_pick(th, Xhat, Y, Z, gamma, c):
    return int(np.argmin(V * gamma * (Xhat - (Y + 1)) + Z * c))


VARIANTS = {
    # Hsu [24] verbatim: I(x) = x^2/2 - x/2 + x/p
    "hsu_on_belief":      lambda th, Xh, Y, Z, g, c: int(np.argmax(
        g * (Xh ** 2 / 2 - Xh / 2 + Xh / np.maximum(th, 1e-9)))),
    "hsu_on_copy_age":    lambda th, Xh, Y, Z, g, c: int(np.argmax(
        g * (Y ** 2 / 2 - Y / 2 + Y / np.maximum(th, 1e-9)))),
    # the index derived for this model's arm
    "derived_2d":         lambda th, Xh, Y, Z, g, c: int(np.argmax([
        g[i] * whittle.index_table(min(max(th[i], 0.01), 0.99))
        [int(np.clip(round(Xh[i]), 0, whittle.K - 1)),
         int(np.clip(round(Y[i]), 0, whittle.K - 1))] for i in range(len(g))])),
    # Eq (13) variations: budget term dropped, or belief replaced by the observed age
    "eq13_on_belief":     lambda th, Xh, Y, Z, g, c: int(np.argmin(
        V * g * (Xh - (Y + 1)) + Z * c)),
    "eq13_no_budget":     lambda th, Xh, Y, Z, g, c: int(np.argmin(
        V * g * (Xh - (Y + 1)))),
    "eq13_on_copy_age":   lambda th, Xh, Y, Z, g, c: int(np.argmin(
        V * g * (Y - (Y + 1)) + Z * c)),
}


def gaps(runs=RUNS):
    """The paired gap of every policy against the oracle, in both `N` panels."""
    print(f"N={N}, m={M}, {runs} runs, tail = last {TAIL} episodes\n")
    rows = []
    for n in (4, 8):
        for Lc, Vc in CELLS:
            got = {p: [] for p in ("oracle", "tsdpp", "lyapunov", "whittle")}
            for r in range(runs):
                for p in got:
                    rng = np.random.default_rng(9000 + r)
                    theta, gamma, c = model.draw_instance(rng, n)
                    pen, _ = model.simulate(theta, gamma, c, M, Lc, p,
                                            np.random.default_rng(9000 + r), Vc)
                    got[p].append(pen[-TAIL:].mean())
            base = np.array(got["oracle"])
            print(f"  N={n}, L={Lc}, V={Vc}")
            for p in ("lyapunov", "whittle", "oracle", "tsdpp"):
                d = np.array(got[p]) - base
                se = d.std(ddof=1) / np.sqrt(runs) if p != "oracle" else 0.0
                print(f"    {p:<10s} tail mean {np.mean(got[p]):8.2f}   "
                      f"paired gap {d.mean():+7.2f} (se {se:.2f})")
                rows.append([n, Lc, Vc, p, round(float(np.mean(got[p])), 4),
                             round(float(d.mean()), 4), round(float(se), 4)])
    os.makedirs(RESULTS, exist_ok=True)
    with open(os.path.join(RESULTS, "paired_gaps.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["N", "L", "V", "policy", "tail_penalty", "paired_gap", "se"])
        w.writerows(rows)
    print(f"\nwrote {os.path.join(RESULTS, 'paired_gaps.csv')}")


def run_variants(runs=RUNS):
    print(f"N={N}, L={L}, V={V}, m={M}, {runs} runs, paired seeds\n")
    base = np.array([_rollout(oracle_pick, 9000 + r, "oracle")[0] for r in range(runs)])
    print(f"oracle tail mean = {base.mean():.2f}\n")
    print(f"{'variant':20s} {'tail mean':>10s} {'paired gap':>12s}  verdict")
    print("-" * 62)
    rows = []
    for name, fn in VARIANTS.items():
        got = np.array([_rollout(fn, 9000 + r)[0] for r in range(runs)])
        d = got - base
        se = d.std(ddof=1) / np.sqrt(runs)
        verdict = ("worse than oracle" if d.mean() > 2 * se else
                   "better than oracle" if d.mean() < -2 * se else "ties oracle")
        print(f"{name:20s} {got.mean():10.2f} {d.mean():+9.2f} (se {se:.2f})  {verdict}")
        rows.append([name, round(float(got.mean()), 4), round(float(d.mean()), 4),
                     round(float(se), 4), verdict])
    os.makedirs(RESULTS, exist_ok=True)
    with open(os.path.join(RESULTS, "baseline_variants.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["variant", "tail_penalty", "paired_gap", "se", "verdict"])
        w.writerows(rows)
    print(f"\nwrote {os.path.join(RESULTS, 'baseline_variants.csv')}")


def whittle_ab(runs=RUNS):
    """Why the derived Whittle index beats both TS-DPP and the paper's oracle.

    Three suspects, tested by turning each off in turn:

      extra spend   the Whittle policy carries no virtual queue, so it could be buying
                    penalty with cost. Adding the same Eq (12) queue back leaves the gap
                    intact while pulling the cost back to the other policies' level.
      known theta   handing it theta* instead of the posterior mean does not help either.
      index itself  what is left is the policy structure: the Whittle index solves the
                    average-reward relaxed problem, Eq (13) is a one-step rule.

    Both reference lines are reported because both get quoted. `vs_tsdpp` is the gap this
    experiment is about; `vs_oracle` is the one Difference 1 and Difference 7 of the README
    read off.
    """
    print(f"N={N}, L={L}, V={V}, m={M}, {runs} runs, paired seeds\n")
    tail, cost, name_of = {}, {}, []
    for name, pick, known in _AB:
        pen = np.empty(runs)
        cs = np.empty(runs)
        for r in range(runs):
            pen[r], cs[r] = _rollout(pick, 9000 + r, "oracle" if known else "plugin")
        tail[name], cost[name] = pen, cs
        name_of.append(name)
    orc, tsd = tail[_AB[0][0]], tail[_AB[1][0]]

    print(f"{'policy':34s} {'tail penalty':>13s} {'vs tsdpp':>18s} {'vs oracle':>18s} "
          f"{'cost':>9s}")
    print("-" * 96)
    rows = []
    for name in name_of:
        d_t, d_o = tail[name] - tsd, tail[name] - orc
        se_t = d_t.std(ddof=1) / np.sqrt(runs)
        se_o = d_o.std(ddof=1) / np.sqrt(runs)
        print(f"{name:34s} {tail[name].mean():13.2f} "
              f"{d_t.mean():+10.2f} (se {se_t:.2f}) "
              f"{d_o.mean():+10.2f} (se {se_o:.2f}) {cost[name].mean():9.4f}")
        rows.append([name, round(float(tail[name].mean()), 4), round(float(d_t.mean()), 4),
                     round(float(se_t), 4), round(float(d_o.mean()), 4),
                     round(float(se_o), 4), round(float(cost[name].mean()), 6)])
    os.makedirs(RESULTS, exist_ok=True)
    with open(os.path.join(RESULTS, "whittle_ab.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["policy", "tail_penalty", "vs_tsdpp", "se_tsdpp",
                    "vs_oracle", "se_oracle", "cost"])
        w.writerows(rows)
    print(f"\nwrote {os.path.join(RESULTS, 'whittle_ab.csv')}")


def _w_index(th, Xh, Y):
    return np.array([
        whittle.index_table(min(max(th[i], 0.01), 0.99))[
            int(np.clip(round(Xh[i]), 0, whittle.K - 1)),
            int(np.clip(round(Y[i]), 0, whittle.K - 1))]
        for i in range(len(th))])


def _ab_oracle(th, Xh, Y, Z, g, c):
    return int(np.argmin(V * g * (Xh - (Y + 1)) + Z * c))


def _ab_whittle(th, Xh, Y, Z, g, c):
    # [24] prescribes no budget control, so this is the unconstrained index policy.
    return int(np.argmax(g * _w_index(th, Xh, Y)))


def _ab_whittle_budget(th, Xh, Y, Z, g, c):
    return int(np.argmax(V * g * _w_index(th, Xh, Y) - Z * c))


_AB = [
    ("oracle  Eq (13), theta known", _ab_oracle, True),
    ("tsdpp   Eq (13)", _ab_oracle, False),
    ("whittle no budget term", _ab_whittle, False),
    ("whittle + budget term", _ab_whittle_budget, False),
    ("whittle + budget, theta known", _ab_whittle_budget, True),
]


def cost(runs=RUNS):
    """Realised cost per policy, with standard errors, and the paired Whittle differences.

    Every policy is rolled out on the *same* instances -- one `default_rng(9000 + r)` draws
    the instance and each policy then consumes its own identically-seeded stream -- so the
    differences below are paired run by run and their standard errors are the standard
    errors of a difference, not those of two pooled means. `runs` defaults to `RUNS`, the
    count every other diagnostic in this file uses; the paper's own Monte Carlo sample is
    1000. The CSV carries `runs` so a reader can tell which count produced the numbers.
    """
    print(f"budget B = {B}, N={N}, L={L}, m={M}, {runs} runs\n")
    print(f"{'policy':22s} {'mean realised cost':>19s} {'se':>9s} "
          f"{'(mean-B)/se':>12s} {'over budget':>13s}")
    print("-" * 80)
    per = {}
    rows = []
    for p in ("oracle", "tsdpp", "lyapunov", "whittle"):
        vals = []
        for r in range(runs):
            rng = np.random.default_rng(9000 + r)
            theta, gamma, c = model.draw_instance(rng, N)
            vals.append(model.simulate(theta, gamma, c, M, L, p,
                                       np.random.default_rng(9000 + r), V)[1])
        per[p] = np.array(vals)
        v = float(per[p].mean())
        se = float(per[p].std(ddof=1) / np.sqrt(runs))
        print(f"{p:22s} {v:19.4f} {se:9.5f} {(v - B) / se:+12.2f} {v - B:+13.4f}")
        rows.append([p, round(v, 6), round(se, 6), round(v - B, 6), runs])

    pairs = [("whittle", "tsdpp"), ("whittle", "lyapunov"), ("whittle", "oracle"),
             ("oracle", "tsdpp")]
    prows = []
    print(f"\npaired against Whittle (same {runs} instances, run by run)")
    print(f"{'difference':22s} {'mean':>10s} {'se':>9s} {'t':>8s}")
    print("-" * 52)
    for a, b in pairs:
        d = per[a] - per[b]
        dm = float(d.mean())
        dse = float(d.std(ddof=1) / np.sqrt(runs))
        print(f"{a + ' - ' + b:22s} {dm:+10.5f} {dse:9.5f} {dm / dse:+8.2f}")
        prows.append([a, b, round(dm, 6), round(dse, 6), runs])

    os.makedirs(RESULTS, exist_ok=True)
    with open(os.path.join(RESULTS, "cost.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["policy", "realised_cost", "se", "over_budget", "runs"])
        w.writerows(rows)
    with open(os.path.join(RESULTS, "cost_paired.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["a", "b", "mean_diff", "se", "runs"])
        w.writerows(prows)
    print(f"\nwrote {os.path.join(RESULTS, 'cost.csv')} and cost_paired.csv")


def carry(runs=1000, synth_runs=200):
    """The episode-boundary choice: Fig. 5's shape, and why it cannot also be Fig. 3's.

    Real-world half. The oracle is the isolation: it knows `theta*` and never learns, so the
    warm-up is the only thing that can differ between the rows. `reset` re-zeroes the AoI at
    every boundary and gives a flat line; `carried` lets it run and gives the paper's rise.

    `carried_z` is the rejected variant that carries the virtual queue across the boundary
    too. Eq (7) averages the realised cost over one episode of length `L`, so `Z` has no
    business crossing it, and the queue runs away when it does -- which is what this row is
    here to show rather than assert. See README Difference 6 and DESIGN.md S-1.

    Synthetic half. The same flag on the setting of Fig. 3 and Fig. 4 sends the curves the
    other way, so no single setting produces both figures. Both `reset` and `carried` are
    measured here rather than argued.
    """
    modes = [("reset", False, False), ("carried", True, False),
             ("carried_z", True, True)]
    theta, stream = realworld.load()
    rows = []

    print(f"real-world setting, oracle only, N={len(theta)}, L={FIG5_L}, "
          f"m={FIG5_M}, {runs} runs\n")
    print(f"{'V':>5s} {'X, Y, Z at the boundary':>24s} {'ep1':>9s} {'ep5':>9s} "
          f"{'ep100':>9s} {'plateau':>9s} {'ep1/plateau':>12s}")
    print("-" * 84)
    for Vc in FIG5_V:
        for label, c_x, c_z in modes:
            acc = np.zeros(FIG5_M)
            for r in range(runs):
                rng = np.random.default_rng(60000 + r)
                n = len(theta)
                gamma, c = rng.dirichlet(np.ones(n)), rng.uniform(0.2, 0.5, n)
                acc += model.simulate(theta, gamma, c, FIG5_M, FIG5_L, "oracle",
                                      np.random.default_rng(60000 + r), Vc,
                                      stream=stream, carry=c_x, carry_z=c_z)[0]
            acc /= runs
            plateau = float(acc[-TAIL:].mean())
            print(f"{Vc:5g} {label:>24s} {acc[0]:9.2f} {acc[4]:9.2f} {acc[-1]:9.2f} "
                  f"{plateau:9.2f} {acc[0] / plateau:12.3f}")
            rows.append(["realworld", Vc, "oracle", label, round(float(acc[0]), 4),
                         round(float(acc[4]), 4), round(float(acc[-1]), 4),
                         round(plateau, 4), round(float(acc[0] / plateau), 4)])

    Lc, Vc = CELLS[0]
    print(f"\nsynthetic setting, N={N}, L={Lc}, V={Vc}, m={M + 50}, {synth_runs} runs "
          f"(Fig. 3's panel)\n")
    print(f"{'policy':>9s} {'X, Y at the boundary':>22s} {'ep1':>9s} {'ep5':>9s} "
          f"{'ep100':>9s} {'plateau':>9s} {'ep1/plateau':>12s}")
    print("-" * 84)
    for p in ("oracle", "tsdpp"):
        for label, c_x, c_z in modes[:2]:
            acc = np.zeros(M + 50)
            for r in range(synth_runs):
                drew = np.random.default_rng(9000 + r)
                th, g, cc = model.draw_instance(drew, N)
                acc += model.simulate(th, g, cc, M + 50, Lc, p,
                                      np.random.default_rng(9000 + r), Vc,
                                      carry=c_x, carry_z=c_z)[0]
            acc /= synth_runs
            plateau = float(acc[-TAIL:].mean())
            print(f"{p:>9s} {label:>22s} {acc[0]:9.2f} {acc[4]:9.2f} {acc[-1]:9.2f} "
                  f"{plateau:9.2f} {acc[0] / plateau:12.3f}")
            rows.append(["synthetic", Vc, p, label, round(float(acc[0]), 4),
                         round(float(acc[4]), 4), round(float(acc[-1]), 4),
                         round(plateau, 4), round(float(acc[0] / plateau), 4)])

    os.makedirs(RESULTS, exist_ok=True)
    with open(os.path.join(RESULTS, "carry.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["setting", "V", "policy", "boundary", "ep1", "ep5", "ep100",
                    "plateau", "ep1_over_plateau"])
        w.writerows(rows)
    print(f"\nwrote {os.path.join(RESULTS, 'carry.csv')}")


def fig7(seeds=300, m=FIG7_M, L=FIG7_L):
    """Is Fig. 7's shaded band calibrated? Nominal 95 percent, measured below.

    The paper describes the band as the 95 percent confidence interval of the beta
    distribution, which is what Eq (14)'s posterior defines. Both the estimator and the
    quantiles come from `model.posterior_path`, the same call the figure is drawn from, so
    this measures the paper's posterior rather than this replica's arithmetic. A calibrated
    interval covers `theta*` in 95 percent of realisations and its mean width tracks the
    root-mean-square error that actually shows up across them.
    """
    theta = np.array(FIG7_THETA)
    n = len(theta)
    checkpoints = [20, 50, m]
    cov = {e: np.zeros(n) for e in checkpoints}
    width = {e: np.zeros(n) for e in checkpoints}
    err = {e: [] for e in checkpoints}
    for s in range(seeds):
        rng = np.random.default_rng(s)
        gamma, c = rng.dirichlet(np.ones(n)), rng.uniform(0.2, 0.5, n)
        mean, lo, hi = model.posterior_path(theta, gamma, c, m, L, rng, FIG7_V)
        for e in checkpoints:
            cov[e] += (lo[e] <= theta) & (theta <= hi[e])
            width[e] += hi[e] - lo[e]
            err[e].append(mean[e] - theta)

    print(f"Fig. 7's Beta(alpha, beta) band, {seeds} realisations, "
          f"m={m}, L={L}, V={FIG7_V}\n")
    print(f"{'episode':>8s} {'theta':>7s} {'coverage':>9s} {'mean err':>10s} "
          f"{'rmse':>8s} {'mean width':>11s}")
    print("-" * 58)
    rows = []
    for e in checkpoints:
        d = np.array(err[e])
        for i, t in enumerate(theta):
            cvg, w = cov[e][i] / seeds, width[e][i] / seeds
            rmse = float(np.sqrt((d[:, i] ** 2).mean()))
            print(f"{e:8d} {t:7.3f} {cvg:9.3f} {d[:, i].mean():+10.4f} "
                  f"{rmse:8.4f} {w:11.4f}")
            rows.append([e, t, round(float(cvg), 4), round(float(d[:, i].mean()), 6),
                         round(rmse, 6), round(float(w), 6), seeds])
    os.makedirs(RESULTS, exist_ok=True)
    with open(os.path.join(RESULTS, "fig7_calibration.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["episode", "theta", "coverage", "mean_err", "rmse", "mean_width",
                    "seeds"])
        w.writerows(rows)
    print(f"\nwrote {os.path.join(RESULTS, 'fig7_calibration.csv')}")


EQ14_SEEDS, EQ14_REF, EQ14_D_SEEDS = 20, 400, 40
EQ14_QUOTED = {False: np.array([0.042, 0.021, 0.002]),
               True: np.array([-0.023, -0.017, -0.007])}
EQ14_PULLS = (50, 100, 200, 400, 800, 1600, 3200, 6400, 25600)


def _rr_rule(n):
    """A round-robin `rule`: arm `counter % n`, so every arm's cadence is exactly `n`."""
    state = [0]

    def rule(theta, Xhat, Y, Z, gamma, c):
        a = state[0] % n
        state[0] += 1
        return a
    return rule


def _eq14_posterior(seed, carry, m=FIG7_M):
    """One `simulate` call at a fixed cadence, with the posterior read back.

    `policy="lyapunov"` only says what the algorithm is told -- the posterior mean -- since
    `rule` overrides arm selection. With a round-robin rule and no stream the rollout is a
    deterministic function of `(seed, carry, m)`: the only rng draw left in the slot loop is
    the event indicator. That is what makes the two `carry` settings comparable seed by seed
    in Experiment C, and what lets Experiment D hold the seed fixed as `m` grows.
    """
    n = len(FIG7_THETA)
    _, gamma, c = model.draw_instance(np.random.default_rng(seed), n)
    posterior = [np.ones(n), np.ones(n)]
    model.simulate(np.array(FIG7_THETA), gamma, c, m, FIG7_L, "lyapunov",
                   np.random.default_rng(seed), FIG7_V, carry=carry,
                   rule=_rr_rule(n), posterior=posterior)
    alpha, beta = posterior
    return alpha, beta, alpha / (alpha + beta)


def _episodes_for(pulls):
    """Episodes needed to give every arm `pulls` pulls at cadence `n`.

    Total pulls is `m * L`, so per-arm is `m * L / n`, rounded up: the first point lands on
    53.3 pulls rather than 50 because `L = 20` is not a multiple of `n = 3`.
    """
    return -(-len(FIG7_THETA) * pulls // FIG7_L)


def _fixed_cadence(g, theta):
    """The per-pull estimator at a gap of exactly `g`, in closed form.

    A pull books `I = 1` iff the age it sees is below the gap, and adds `I` to `alpha` and
    the age to `beta`; over a gap of exactly `g` the age has `P(age = s) = theta
    (1 - theta)^s`, so the estimator's expectation per pull is
    `(1 - (1-theta)^g) / (sum_{s<g} (1+s) theta (1-theta)^s + g (1-theta)^g)`.
    That ratio is `theta` identically, for every `g`: see Experiment B.
    """
    num = 1 - (1 - theta) ** g
    den = (sum((1 + s) * theta * (1 - theta) ** s for s in range(g))
           + g * (1 - theta) ** g)
    return num, den, num / den


def eq14(seeds=EQ14_SEEDS, ref=EQ14_REF):
    """Where Fig. 7's posterior bias comes from: the episode boundary, not Eq (14).

    Three experiments, all on the round-robin cadence of `n = 3` over the paper's three
    `theta` values, `L = 20`, `m = 100` episodes in ONE `simulate` call:

    A  the bias is still there when the policy is taken out of the loop. Running the very
       same call with `carry=True` moves it, so the arm-selection layer cannot be the
       cause -- and Experiment B rules out the update rule, which leaves the boundary.
    B  `theta_hat == theta` exactly at every cadence, at floating-point noise, so Eq (14)
       is not biased when the cadence is genuinely fixed.
    C  the artifact's size, read off the final `alpha` and `beta` of two runs on the same
       seed. The first pull of each arm in each episode is scored against `t_prev = 0` and
       `s_prev = 0`: the local clock and the local age are both re-zeroed, so the estimator
       is told the arm was never pulled and never saw an event in this episode.

    The quoted column of A is the reference table this subcommand exists to reproduce.
    """
    n = len(FIG7_THETA)
    theta = np.array(FIG7_THETA)
    a_ref = {c: np.empty((ref, n)) for c in (False, True)}
    ab_ref = {c: (np.zeros(n), np.zeros(n)) for c in (False, True)}
    for s in range(ref):
        for c in (False, True):
            al, be, mean = _eq14_posterior(s, c)
            a_ref[c][s] = mean
            ab_ref[c][0][:] += al
            ab_ref[c][1][:] += be
    ab_head = {c: (np.zeros(n), np.zeros(n)) for c in (False, True)}
    for s in range(seeds):
        for c in (False, True):
            al, be, _ = _eq14_posterior(s, c)
            ab_head[c][0][:] += al / seeds
            ab_head[c][1][:] += be / seeds

    print(f"A. Eq (14) at a fixed cadence of n={n}: round-robin rule, policy told the "
          f"posterior mean,\none simulate call of m={FIG7_M} episodes of L={FIG7_L} slots, "
          f"{seeds} seeds (reference column: {ref})\n")
    print(f"{'carry':>6s} {'theta':>7s} {'bias':>9s} {'se':>7s} {'quoted':>8s} "
          f"{'dev':>8s} {'bias_ref':>9s} {'se_ref':>7s} {'dev_ref':>8s}")
    print("-" * 76)
    rows = []
    for c in (False, True):
        d_ref = a_ref[c] - theta
        for i, t in enumerate(theta):
            d = d_ref[:seeds, i]
            se, m = d.std(ddof=1) / np.sqrt(seeds), float(d.mean())
            se_r, m_r = (d_ref[:, i].std(ddof=1) / np.sqrt(ref), float(d_ref[:, i].mean()))
            q = EQ14_QUOTED[c][i]
            print(f"{str(c):>6s} {t:7.3f} {m:+9.4f} {se:7.4f} {q:+8.3f} {m - q:+8.4f} "
                  f"{m_r:+9.4f} {se_r:7.4f} {m_r - q:+8.4f}")
            rows.append(["A", int(c), "", "", round(t, 4), "", "bias", round(m, 6),
                         round(se, 6), round(m_r, 6), round(q, 4), round(m - q, 6)])
    print(f"\n   bias = mean over seeds of (posterior mean - theta*). The quoted column is "
          f"the target table;\n   the {ref}-seed column is the same quantity measured "
          f"properly. A {seeds}-seed window of the\n   reference itself lands within "
          f"+-0.005 of that column for:")
    for c in (False, True):
        d_ref = a_ref[c] - theta
        ok = sum(1 for b in range(ref - seeds + 1)
                 if np.abs(d_ref[b:b + seeds].mean(0) - EQ14_QUOTED[c]).max() <= 0.005)
        print(f"     carry={str(c):<5s} {ok:4d} of {ref - seeds + 1} windows "
              f"(so the residual is the estimate's own spread, not a different model)")

    print(f"\nB. the same estimator at a genuinely fixed cadence, in closed form "
          f"(no simulation)\n")
    print(f"{'g':>3s} {'theta':>7s} {'E[d alpha]':>11s} {'E[d beta]':>11s} "
          f"{'theta_hat':>10s} {'residual':>12s}")
    print("-" * 60)
    for g in (1, 2, 3, 5):
        for t in theta:
            num, den, hat = _fixed_cadence(g, float(t))
            print(f"{g:3d} {t:7.3f} {num:11.6f} {den:11.6f} {hat:10.6f} "
                  f"{hat - t:+12.3e}")
            rows.append(["B", "", g, "", round(t, 4), "", "theta_hat", round(hat, 16), "",
                         "", round(t, 4), round(hat - t, 18)])

    print(f"\nC. the boundary artifact: same seed, round-robin cadence {n}, carry=False (F) "
          f"vs carry=True (T)\n")
    print(f"   delta_alpha = alpha(F) - alpha(T), delta_beta = beta(F) - beta(T), "
          f"delta_mean = mean(F) - mean(T),\n   all per arm. F zeroes the AoI at the "
          f"boundary, so the first pull of arm a in an episode\n   reads s <= t-1 < t = "
          f"n_gap and MUST book I=1: a success against a gap the arm did not\n   serve. T "
          f"scores the carried age against the same truncated clock. If F's forced success\n"
          f"   were the whole difference, delta_alpha would be m-1 = {FIG7_M - 1} per arm. "
          f"Same rows in the CSV\n   as alpha_false / alpha_true / beta_false / beta_true / "
          f"d_mean.\n")
    print(f"{'seed':>6s} {'arm':>4s} {'theta':>7s} {'alpha F':>9s} {'alpha T':>9s} "
          f"{'delta_alpha':>12s} {'beta F':>9s} {'beta T':>9s} {'delta_beta':>11s} "
          f"{'delta_mean':>11s}")
    print("-" * 110)
    one = {}
    for label, s in (("seed 0", 0), (f"{seeds}-seed mean", None)):
        if s is None:
            af, bf = ab_head[False]
            at, bt = ab_head[True]
        else:
            af, bf, _ = _eq14_posterior(s, False)
            at, bt, _ = _eq14_posterior(s, True)
            one = {False: (af, bf), True: (at, bt)}
        for i, t in enumerate(theta):
            da, db = af[i] - at[i], bf[i] - bt[i]
            dm = af[i] / (af[i] + bf[i]) - at[i] / (at[i] + bt[i])
            print(f"{label:>6s} {i:4d} {t:7.3f} {af[i]:9.2f} {at[i]:9.2f} {da:+12.2f} "
                  f"{bf[i]:9.2f} {bt[i]:9.2f} {db:+11.2f} {dm:+11.4f}")
            rows.append(["C", "", "", "", round(t, 4), i, "alpha_false",
                         round(float(af[i]), 4), "", round(float(at[i]), 4), "",
                         round(float(da), 4)])
            rows.append(["C", "", "", "", round(t, 4), i, "beta_false",
                         round(float(bf[i]), 4), "", round(float(bt[i]), 4), "",
                         round(float(db), 4)])
            rows.append(["C", "", "", "", round(t, 4), i, "d_mean", round(float(dm), 6),
                         "", "", "", ""])
    af, bf = one[False]
    at, bt = one[True]
    print(f"\n   seed 0, all arms: delta_alpha sums to {float((af - at).sum()):.0f} against "
          f"m={FIG7_M} episodes, delta_beta to {float((bf - bt).sum()):.0f}.")
    d_a = ab_head[False][0] - ab_head[True][0]
    fmt = lambda v: "/".join(f"{x:.1f}" for x in v)
    print(f"   Measured delta_alpha is {fmt(d_a)} per arm at the {seeds}-seed mean, "
          f"against m-1 = {FIG7_M - 1}\n   boundaries: meaningfully SMALLER, not equal -- "
          f"that is {fmt(100 * d_a / (FIG7_M - 1))} percent of boundaries. F's "
          f"forged success\n   is real and happens at every boundary, but T books a success "
          f"at most of the same\n   boundaries too: the reset only changes the answer where "
          f"the carried age beats the\n   episode-local clock, and t <= L = {FIG7_L} while "
          f"the carried age is geometric with mean\n   (1-theta)/theta. So 'm-1' would "
          f"overstate the difference; the right statement is one forced\n   success per arm "
          f"per episode in F, of which delta_alpha sees only the fraction where T\n   "
          f"disagrees. delta_beta is the larger effect and is charged to T, not to F: the\n"
          f"   whole carried age lands in beta as a run of failures, which is what drags "
          f"the T\n   posterior mean down.")

    print(f"\nD. does the bias decay as pulls accumulate? carry=False, round-robin cadence "
          f"{n}, {EQ14_D_SEEDS} seeds\n")
    print(f"   pulls/arm is what the rollout actually gives at m = ceil({n} * target / "
          f"{FIG7_L}) episodes; a constant\n   'bias x pulls' would mean the bias is a "
          f"1/count effect that washes out, a growing one that it is\n   a fixed offset "
          f"that never does\n")
    print(f"{'pulls/arm':>10s} {'theta':>7s} {'bias':>10s} {'se':>8s} {'bias*pulls':>12s} "
          f"{'se*pulls':>9s}")
    print("-" * 62)
    got, realized = {}, []
    for target in EQ14_PULLS:
        m = _episodes_for(target)
        pulls = m * FIG7_L / n
        realized.append(pulls)
        res = np.empty((EQ14_D_SEEDS, n))
        for s in range(EQ14_D_SEEDS):
            res[s] = _eq14_posterior(s, False, m=m)[2]
        d = res - theta
        b, se = d.mean(0), d.std(0, ddof=1) / np.sqrt(EQ14_D_SEEDS)
        got[pulls] = b
        for i, t in enumerate(theta):
            print(f"{pulls:10.1f} {t:7.3f} {b[i]:+10.4f} {se[i]:8.4f} "
                  f"{b[i] * pulls:12.1f} {se[i] * pulls:9.1f}")
            rows.append(["D", 0, "", pulls, round(t, 4), "", "bias", round(float(b[i]), 6),
                         round(float(se[i]), 6), "", "", ""])
            rows.append(["D", 0, "", pulls, round(t, 4), "", "bias_x_pulls",
                         round(float(b[i] * pulls), 3), round(float(se[i] * pulls), 3),
                         "", "", ""])
    p_lo, p_hi = realized[-3], realized[-1]
    print(f"\n   bias*pulls per arm for theta={theta[0]:.3f}: "
          f"{got[realized[0]][0] * realized[0]:.1f} at {realized[0]:.0f} pulls -> "
          f"{got[realized[-2]][0] * realized[-2]:.0f} at {realized[-2]:.0f} -> "
          f"{got[p_hi][0] * p_hi:.0f} at {p_hi:.0f}: it grows without bound.")
    print(f"   So the bias is NOT a 1/count effect. From {p_lo:.0f} to {p_hi:.0f} pulls the "
          f"count rises {p_hi / p_lo:.0f}x\n   while the bias moves by a factor of "
          f"{'/'.join(f'{x:.3f}' for x in got[p_hi] / got[p_lo])} per arm -- a constant "
          f"offset that survives every pull budget\n   measured here, which is the README "
          f"claim. The small-count "
          f"end is inflated by the Beta(1,1)\n   prior pulling toward 0.5, so the flat tail "
          f"is not the prior washing out.")

    os.makedirs(RESULTS, exist_ok=True)
    with open(os.path.join(RESULTS, "eq14.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["experiment", "carry", "g", "pulls", "theta", "arm", "statistic",
                    "value", "se", "ref_value", "expected", "delta"])
        w.writerows(rows)
    print(f"\nwrote {os.path.join(RESULTS, 'eq14.csv')}")


if __name__ == "__main__":
    what = sys.argv[1] if len(sys.argv) > 1 else "variants"
    {"gaps": gaps, "variants": run_variants, "whittle": whittle_ab, "cost": cost,
     "carry": carry, "fig7": fig7, "eq14": eq14}[what]()
