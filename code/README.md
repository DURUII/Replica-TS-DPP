# TS-DPP: Experimental replication

English | [中文](README.zh.md)

## How to run

> Developed and tested on Apple M4, macOS 26.2 (25C56), Python 3.13.5.

Experimental parameters follow Section V: `theta_i ~ U[0,1]`, `gamma ~ Dirichlet` with `sum gamma = 1`,
`c_i ~ U[0.2, 0.5]`, `B = 0.35`.

The paper runs 50 episodes in the synthetic experiments. This project stores 100 episodes: Fig. 3 and Fig. 4 plot the first 50; Fig. 6 and Fig. 7 use the full length. See [Penalty levels differ; growth ratios are close](#difference-4).

Run from the `code/` directory:

```
pip install numpy scipy matplotlib markovianbandit-pkg numba
python src/run.py all          # simulations  -> results/*.csv
python src/plot/draw.py        # results/*.csv -> figs/*.png
python src/diagnose.py gaps    # the evidence behind "Differences" below
python src/diagnose.py whittle # why the Whittle baseline lands below the oracle
```

`markovianbandit-pkg` declares no dependencies in its metadata but imports `numba` and
`scipy` at load time, so those must be installed explicitly.

## Differences at a glance

The paper provides no experiment code and leaves baseline implementations, data slices, and episode boundary handling unspecified. To test whether these choices cause the discrepancies, we compare baseline implementations, budget control, and boundary handling, and check published figure readings against simulation data.

| No. | Difference | Summary |
| --- | --- | --- |
| 1 | [Baseline ordering](#difference-1) | In synthetic experiments, episode resets and the Whittle index derived for this problem place Whittle below the oracle in penalty, reversing Fig. 3 and Fig. 4. Episode boundary handling also changes the ordering, so index choices and boundaries must be considered together. |
| 2 | [Whittle baseline](#difference-2) | The cited index assumes a different age reset, and the paper does not specify its adaptation. Direct use reproduces the direction of the reported ordering; deriving a two-dimensional index for the current problem reverses it. |
| 3 | [Lyapunov baseline](#difference-3) | The posterior-mean DPP implementation gives a smaller gap from the oracle than the paper reports. Using observed age makes the gap too large; no tested implementation reproduces both its direction and magnitude. |
| 4 | [Penalty levels and run length](#difference-4) | The penalty increase from N = 4 to N = 8 is close to the paper, but absolute levels differ. Independent repetition counts are unspecified, and low-event-rate samples affect across-run means. This replica stores 100 episodes and plots the first 50 for Fig. 3 and Fig. 4. |
| 5 | [Regret definition](#difference-5) | The paper does not specify normalization or the comparison baseline for time-averaged regret. This replica uses the oracle and averages cumulative episode regret; decay trends can be compared, while ordinate values are not directly comparable. |
| 6 | [Real data and episode boundaries](#difference-6) | The data month and slice are unspecified. Event counts lead to three December 2019 event types, with a remaining 0.44% discrepancy. Carrying age states approaches Fig. 5's shape and levels, but the same choice changes synthetic curves and ordering. |
| 7 | [Budget constraint](#difference-7) | At the current settings, Whittle without a budget queue has mean cost close to the budget, while queue-carrying policies spend slightly less. Giving Whittle the same queue preserves its penalty advantage; cost differences explain only part of the result. |
| 8 | [Estimation bias and interval coverage](#difference-8) | Persistent estimation bias remains, while frequentist coverage of the Beta 95% credible intervals declines across episodes. Diagnostics locate persistent bias at episode-boundary history resets; reset and carry induce opposite bias directions. |

## Differences from the paper

### Reading notation

| Symbol or term | Meaning |
| --- | --- |
| `se` (standard error) | Uncertainty in an estimated mean; smaller values indicate greater precision |
| Tail penalty | Mean penalty over the final 10 episodes |
| `reset` | Reset age at the start of each episode |
| `carry` | Preserve age between episodes |

All baselines run in the online setting with unknown transition probabilities. The oracle uses the true parameters; the other policies use posterior samples or means. Policies with a virtual queue control the budget using Eq. (12). Their implementations are listed below:

| Policy | Parameter estimate | Selection rule |
| --- | --- | --- |
| Belief-DPP (oracle) | `theta*` | Eq. (13) |
| TS-DPP | one draw from the Beta posterior per episode | Eq. (13) |
| Lyapunov [20] | posterior mean | Eq. (13) — the same rule |
| Whittle [24] | posterior mean | [the Whittle index derived for this problem](#difference-2), `argmax gamma_i * I_i(x, y)` |

<a id="difference-1"></a>

### 1. Baseline ordering reversed

#### Difference

Every panel of the paper's Fig. 3 and Fig. 4 orders the penalties as follows:

```
TS-DPP ~ Belief-DPP (oracle)  <  Lyapunov [20]  <  Whittle [24]
```

This replica uses episode resets (`reset`) and the two-dimensional Whittle index for this model in the synthetic experiments. Whittle has a lower penalty than the oracle. Both the index and the episode boundary affect the ordering: [The Whittle index depends on the age reset](#difference-2) compares indices; [Trace selection and episode boundaries](#difference-6) shows that carrying the age state (`carry`) makes Whittle's penalty the highest.

#### Explanation

The oracle runs the drift-plus-penalty rule of Eq. (13) with the true parameter `theta*`; the Whittle index solves an average-reward relaxed problem. The oracle is a DPP policy with known parameters; Whittle chooses arms through a different optimization.

#### Tests

##### Figure readings and paired comparisons

At `L = 20, V = 0.2`, `python scripts/measure_fig_levels.py` reads each published panel against its own tick marks. `python src/diagnose.py gaps` reports paired penalty gaps relative to the oracle:

| Policy | Paper, Fig. 3(a) `N = 4` | Paper, Fig. 4(a) `N = 8` | This replica, `N = 4` (200 runs) |
| --- | --- | --- | --- |
| Lyapunov | `+1.71` | `+2.69` | `+0.42` (se 0.09) |
| Whittle | `+4.45` | `+8.40` | `-2.84` (se 0.25) |
| TS-DPP | `+0.01` | `+0.14` | `-0.25` (se 0.51) |

TS-DPP is within half a standard error of the oracle. The Lyapunov gap agrees in direction and is about one quarter of the paper's Fig. 3(a) gap; see [The Lyapunov penalty gap remains unreproduced](#difference-3). Whittle is below the oracle in all eight parameter settings, with paired gaps from `-2.8` to `-4.7` over 200 runs per setting (`results/paired_gaps.csv`).

##### Budget and true-parameter controls

With `reset` fixed, `python src/diagnose.py whittle` adds the virtual queue of Eq. (12) to Whittle and then supplies the true parameter `theta*` (`results/whittle_ab.csv`):

| Variant | Tail penalty | vs. posterior-mean DPP | vs. oracle | Realised cost |
| --- | --- | --- | --- | --- |
| Belief-DPP (oracle), `theta*` known | `77.21` | `-0.42` (se 0.09) | `+0.00` | `0.3467` |
| DPP, posterior mean | `77.63` | `+0.00` | `+0.42` (se 0.09) | `0.3471` |
| Whittle index, no budget term | `74.37` | `-3.26` (se 0.25) | `-2.84` (se 0.25) | `0.3514` |
| Whittle index + Eq. (12) queue | `74.47` | `-3.16` (se 0.25) | `-2.74` (se 0.25) | `0.3485` |
| Whittle index + queue, `theta*` known | `74.57` | `-3.06` (se 0.28) | `-2.64` (se 0.27) | `0.3484` |

The DPP reference in this control uses the posterior mean, as does Lyapunov in the shared setup. Adding the queue lowers Whittle's cost from `0.3514` to `0.3485` while retaining a penalty advantage of `2.74` over the oracle. Supplying `theta*` leaves an advantage of `2.64`.

#### Conclusion

Under `reset`, both controls retain Whittle's penalty advantage. The index comparison supports an effect of policy structure, while the boundary comparison shows that the ordering depends on episode handling. The paper does not specify its Whittle implementation, so the discrepancy cannot yet be assigned to a single factor.

<a id="difference-2"></a>

### 2. The Whittle index depends on the age reset

#### Difference

The paper cites [24] (Hsu, Modiano, Duan) without specifying how its Whittle index is adapted to this model. The cited closed form is:

```
I(x) = x^2/2 - x/2 + x/p
```

See Hsu et al., [Scheduling Algorithms for Minimizing Age of Information in Wireless Broadcast Networks with Random Arrivals](https://www.mit.edu/~modiano/papers/CV_J_110.pdf), Theorem 17.

#### Explanation

This formula assumes that serving an arm resets its age to `1`. In this model, pulling PoI `a` sets `Y_a := X_a + 1` under Eq. (4), so the copy age depends on the current event age. A single age cannot describe this transition; the arm state must contain `(event age x, copy age y)`. Substituting the event age directly into Hsu's formula prioritises older events.

#### Tests

`python src/diagnose.py variants` compares each variant with the oracle using paired seeds (`results/baseline_variants.csv`):

| Variant | Paired penalty gap vs. oracle | Result |
| --- | --- | --- |
| Hsu's closed form, belief state | `+70.7` (se 2.7) | higher penalty |
| Hsu's closed form, observed copy age | `+17.9` (se 1.6) | higher penalty |
| Index for this model's two-dimensional arm | `-2.84` (se 0.25) | lower penalty |

Both direct substitutions reproduce the direction of the paper's ordering; the two-dimensional index reverses it. `src/sim/whittle.py` uses `(event age, copy age)` as the state and supplies transition probabilities and rewards for activating or leaving the arm passive. It then calls [`markovianbandit-pkg`](https://pypi.org/project/markovianbandit-pkg/) to compute each state's Whittle index.

A subsidy is a reward for leaving an arm passive. Increasing it makes passivity more attractive. The subsidy at which activation and passivity have equal optimal long-run value is that state's Whittle index. A higher index means more compensation is needed to make passivity optimal.

The package's current implementation uses the algorithm of Gast, Khun, and Gaujal to compute the thresholds in increasing order and check indexability: whether the set of states where passivity is optimal only expands as the subsidy increases. This project calls `whittle_indices()`. See [Testing Indexability and Computing Whittle and Gittins Index in Subcubic Time](https://arxiv.org/abs/2203.05207), Algorithm 2.

#### Conclusion

The comparison shows that age transitions and index implementation can change the baseline ordering. Hsu's formula assumes a different transition and cannot be used directly as this model's index. The paper's adaptation remains unspecified.

<a id="difference-3"></a>

### 3. The Lyapunov penalty gap remains unreproduced

#### Difference

This replica's Lyapunov penalty exceeds the oracle's by `0.42` (se `0.09`), below the paper's gaps of `1.71` in Fig. 3(a) and `2.69` in Fig. 4(a). The paper cites [20] without specifying its implementation for this model.

#### Explanation

The index in [20] has denominator `(1 + phi_n(alpha) / lambda_n)`, involving frame-length and idle parameters. This arm model has no corresponding parameters, so the replica uses the un-normalised numerator. Eq. (13) is already the drift-plus-penalty rule for the quadratic Lyapunov function `L(Z) = Z^2 / 2`. Lyapunov and the oracle therefore share Eq. (13) in this replica, using the posterior mean and the true parameter `theta*`, respectively.

#### Tests

`python src/diagnose.py variants` compares the belief of Eq. (16) with the observed copy age as inputs (`results/baseline_variants.csv`):

| Input to Eq. (13) | Paired penalty gap vs. oracle |
| --- | --- |
| Belief, posterior mean | `+0.42` (se 0.09) |
| Observed copy age | `+43.9` (se 1.8) |

#### Conclusion

Using the observed copy age produces a gap an order of magnitude above the paper's roughly `+2`. The tested implementations do not reproduce both the direction and magnitude of the gap. The Lyapunov baseline discrepancy remains unresolved.

<a id="difference-4"></a>

### 4. Penalty levels differ; growth ratios are close

#### Difference

From `N = 4` to `N = 8`, the paper and replica show similar growth ratios but different penalty levels.

#### Explanation

At `N = 4`, the replica's mean and median differ by `5.6` (se `1.1`), suggesting that a few high-penalty instances influence the mean. Under `theta ~ U[0,1]`, the cross-parameter expectation of the stationary event age, `E[(1 - theta) / theta]`, diverges; very small `theta` may produce long tails. A finite horizon truncates age growth, so this stationary calculation only suggests sensitivity of the mean. The paper states `m = 50` episodes but does not state how many independent draws of `theta*` it averages. The source of the level offset remains unresolved.

#### Tests

The y-axis spans `65.6`–`78.8` in Fig. 3(a) and `86.5`–`103.2` in Fig. 4(a); the panel used for the reading has `2.0`-unit tick spacing. Readings against each panel's ticks (`python scripts/measure_fig_levels.py`) compare with the oracle entries in `results/penalty_tails.csv` as follows:

| | Fig. 3(a), `N = 4` | Fig. 4(a), `N = 8` | Ratio |
| --- | --- | --- | --- |
| Paper, Belief-DPP (oracle) | `66.74` | `87.89` | `1.32` |
| Replica, oracle median | `70.44` | `92.12` | `1.31` |
| Replica, oracle mean | `76.05` | `95.48` | `1.26` |

The paper's ratio is `1.32`; the replica's median ratio is `1.31`, a difference of `0.01`, and its mean ratio is `1.26`. Replica means exceed the paper's levels by `9.3` and `7.6`; medians exceed them by `3.7` and `4.2`. Doubling the penalty with `N` would put Fig. 4(a) at about `133`, above its axis maximum of `103.2`. The penalty is `sum_i gamma_i Y_i`, with `sum_i gamma_i = 1`; this weighted average does not require proportional growth with the arm count.

#### Conclusion

Growth ratios are close; the absolute level offset remains unresolved.

The paper's Fig. 3 and Fig. 4 stop at episode 50. `src/plot/draw.py` uses the same 0..50 window; its CSV holds 100 episodes for Fig. 6 and Fig. 7. Changing `HORIZON` changes the plotting window without re-simulation.

<a id="difference-5"></a>

### 5. The regret definition is unclear

#### Difference

The paper does not specify the normalisation or comparison policy for the time-averaged regret in Fig. 6. Its ordinate cannot be matched directly to the replica's.

#### Explanation

Average regret depends on the reference policy and normalization. This replica uses the oracle and divides cumulative episode regret by the number of episodes.

#### Tests

##### Paper readings

`python scripts/measure_fig_levels.py` reads five first-episode values between `2264` and `3925` in Fig. 6. Four curves are TS-DPP at `V = 0.5, 1, 5, 10`. The legend labels two curves `L = 20, V = 0.5`; this project identifies the dashed curve as the theorem's upper bound from the accompanying text.

The real-data experiment in Fig. 5 uses `N = 3, L = 20` and shows episodic penalties of about `60`–`200`: its lowest first point is `63.2`, and its highest plateau is `190.3`. Fig. 6's initial values are `11`–`20` times `200`, or `226`–`392` times a per-slot penalty of `10`. These readings show a large difference in scale. Fig. 6 uses synthetic data, so Fig. 5 cannot bound its penalty or rule out every possible regret definition.

##### Replica definition and results

This project uses the oracle as its comparison policy and plots the mean cumulative episodic Bayesian regret:

```
Delta_l          = E_{theta*}[ pen_l(policy) ] - E_{theta*}[ pen_l(oracle) ]
time-averaged(l) = (1/l) * sum_{j<=l} Delta_j
```

Theorem 2's bound contains an unspecified constant. For plotting, it is scaled to share the empirical curve's episode-1 anchor. This comparison shows the decay trend: the empirical value reaches `0.53` at episode 100, where the scaled bound is `2.3` times higher; its largest ratio is `2.8`. This result does not validate the theorem's bound constant.

The replica's four `V` curves nearly coincide. Endpoints are `0.535` at `V = 0.5` and `0.563` at `V = 1`; the reported endpoint variation is below 6%, consistent with estimation error dominating regret. The paper's four TS-DPP curves start between `2264` and `3578` and plateau between `19` and `116`, a roughly sixfold spread; the text describes all four as converging. A comparison against an optimal policy that changes with `V` could also change regret's dependence on `V`. The paper does not specify this choice. Both the normalisation and comparison policy remain unresolved.

<a id="difference-6"></a>

### 6. Trace selection and episode boundaries

#### Difference

The paper's Fig. 3, Fig. 4 and Fig. 6 use synthetic data; Fig. 5 uses a real trace at `V ∈ {0.04, 0.06, 0.08, 0.10}`. Reference [31] gives a Kaggle dataset address but leaves the month, file version, window selection and episode boundary handling unspecified. This project selects three December 2019 event types by their count and carries age states between episodes, obtaining a shape and level close to Fig. 5.

#### Explanation

##### Slice selection

The paper maps timestamps to 1-second slots, excludes one infrequent event type and reports `1,654,771` occurrences across the remaining three. Following that description, this project merges occurrences of the same type within each second. Counts of rows, occupied slots, distinct users and distinct `(user, item)` pairs were compared across five monthly files and all two-, three- and four-type subsets:

| Slice | Count | Difference | Relative difference |
| --- | --- | --- | --- |
| 2019-Dec `view` + `cart` + `remove_from_cart`, occupied slots | 1,647,519 | −7,252 | −0.44% |
| 2019-Oct `view` + `cart` + `purchase`, occupied slots | 1,645,164 | −9,607 | −0.58% |
| 2020-Jan `view` + `purchase`, distinct `(user, item)` | 1,662,767 | +7,996 | +0.48% |
| 2019-Dec `cart` + `remove_from_cart` + `purchase`, rows | 1,804,955 | +150,184 | +9.1% |

The first row meets both the three-type requirement and a count difference below 0.5%. December `purchase` occupies `29,137` seconds, against at least `422,184` for each of the other three types. The three frequent types total at least `1,717,728` in each of the other four months. These results support the December `view`, `cart`, `remove_from_cart` selection; the paper's exact slice remains unknown. The five current files are dated `2020-03-16`; a different snapshot could explain the remaining `0.44%` count gap.

The first row can be checked from `data/2019-Dec-3types.npz`. The other three rows, the `purchase` count, other monthly counts and file dates come from a single reading of the raw monthly CSVs, which are not included in this repository.

##### Replay settings

The trace gives `theta_hat = (0.4391, 0.2702, 0.1576)`, the occupied-slot proportions per second for `view`, `cart` and `remove_from_cart`. `gamma`, `c` and `B` follow the configuration Section V-A-1 states applies to all simulations: Dirichlet with `sum gamma = 1`, `U[0.2, 0.5]` and `0.35`. Direct replay preserves burstiness and yields levels closer to the paper than resampling from `Bernoulli(theta_hat)`. The paper states a Monte Carlo sample size of `1000` for Fig. 6 but gives no run count for Fig. 5. This replica uses `1000` runs, drawing a fresh instance each time and using the same draw across the four `V` values to keep the panels paired.

#### Tests

With the trace, `theta_hat` and other parameters fixed, only the handling of `X, Y` between episodes changes. The oracle knows the true parameters and does not learn, isolating the age warm-up effect. Results at `V = 0.06` compare with the paper's Fig. 5(b) as follows:

| `X, Y` boundary handling | Episode 1 | Episode 5 | Plateau | First point / plateau |
| --- | --- | --- | --- | --- |
| Reset to 0, oracle | 96.9 | 98.2 | 98.7 | 0.981 |
| Carried over, oracle | 96.9 | 151.1 | 154.6 | 0.627 |
| Paper Fig. 5(b), TS-DPP | `63.2` | `124.5` | `145.9` | `0.43` |
| Paper Fig. 5(b), Lyapunov | `69.9` | `133.3` | `155.5` | `0.45` |
| Paper Fig. 5(b), Whittle | `83.0` | `150.1` | `173.2` | `0.48` |

The first two rows come from `python src/diagnose.py carry`, which reports every `V`. The last three come from `python scripts/measure_fig_levels.py`. The paper does not plot the oracle in Fig. 5.

Both variants reset the virtual queue `Z` at each episode, corresponding to Eq. (7)'s episodic average-cost constraint. In a separate test carrying `Z`, the queue keeps growing and the penalty reaches `321` at episode 100 for `V = 0.06`, still trending upward; queue-free Whittle remains bounded. The `carry` flag in `simulate` therefore carries only `X, Y`.

With `X, Y` carried and the event rates unchanged, policy plateaus approach the paper's: Lyapunov `154.4` versus `155.5`, TS-DPP `155.4` versus `145.9`, and Whittle `188.0` versus `173.2` (`results/realworld_curves.csv`). On fixed data, the oracle plateau rises from about `99` to `154.6`, showing that age boundary handling explains a substantial part of the level offset.

Applying the same `carry` setting to synthetic experiments matches the paper's Whittle ordering but produces rising curves: at `N = 4, L = 20, V = 0.2`, the first-point/plateau ratio is `0.57` for both the oracle and TS-DPP, whereas the paper's Fig. 3 and Fig. 4 fall. Neither tested boundary setting reproduces the shapes of both the synthetic and real-data figures. This project therefore uses `reset` for synthetic experiments and `carry` for the continuous trace. Whittle has the lowest penalty under `reset` and the highest under `carry`; the reversal in [Baseline ordering reversed](#difference-1) also depends on this boundary choice.

#### Conclusion

The replica's first points remain higher and recovery faster in Fig. 5. TS-DPP starts at `0.67` of its plateau versus the paper's `0.43`; Lyapunov starts at `0.65` versus `0.45`. At episode 5 their ratios are `1.02` and `0.98`, versus `0.85` and `0.86` in the paper. Age rebuilding within 20 slots may depend on the trace window's position, which the paper does not specify. The slice count also differs by `0.44%`. These tests establish this implementation's sensitivity to boundary handling; the paper's actual slice and boundary convention remain unknown. Whittle has the highest penalty in all four Fig. 5 panels, matching the paper. [Baseline ordering reversed](#difference-1) concerns Fig. 3 and Fig. 4 only.

##### Data source and reconstruction

The dataset comes from the REES46 Marketing Platform, published on Kaggle by Michael Kechinov as [`mkechinov/ecommerce-events-history-in-cosmetics-shop`](https://www.kaggle.com/datasets/mkechinov/ecommerce-events-history-in-cosmetics-shop). Its licence is listed as “Data files (c) Original Authors”. `data/2019-Dec-3types.npz` stores per-second bitmaps of the three December 2019 types for direct Fig. 5 replay. The extraction program is `src/sim/extract.py`; raw monthly files are not redistributed. Download and rebuild with:

```
curl -L -o cosmetics.zip \
  "https://www.kaggle.com/api/v1/datasets/download/mkechinov/ecommerce-events-history-in-cosmetics-shop"
unzip -d cosmetics cosmetics.zip                        # five monthly CSVs, 2019-Oct to 2020-Feb
python src/sim/extract.py cosmetics/2019-Dec.csv.gz     # -> data/2019-Dec-3types.npz
```

<a id="difference-7"></a>

### 7. Budget control lowers mean cost

#### Difference

At the current settings, Whittle without a virtual queue has mean cost close to `B = 0.35`; the three DPP policies with a queue spend slightly less.

#### Explanation

The paper sets `B` to the expected cost of uniformly random arm selection. With `c_i ~ U[0.2, 0.5]`, this expectation across instances is `0.35`. A selection rule independent of costs has the same across-instance expectation; costs in an individual instance can still exceed or fall below the budget. Whittle [24] specifies no budget control, so this implementation has no queue. The other policies update their queues using Eq. (12).

#### Tests

`python src/diagnose.py cost` compares mean costs on the same 200 instances:

| Policy | Realised mean cost | Standard error | `(mean − B) / standard error` |
| --- | --- | --- | --- |
| Belief-DPP (oracle) | `0.3467` | `0.0036` | `-0.9` |
| TS-DPP | `0.3469` | `0.0036` | `-0.9` |
| Lyapunov [20] | `0.3471` | `0.0036` | `-0.8` |
| Whittle [24], no queue | `0.3514` | `0.0035` | `+0.4` |

Whittle's mean is `0.4` standard errors above the budget; the three DPP policies are about `0.8%` to `0.9%` below it. Paired comparisons in `results/cost_paired.csv` show Whittle spending `0.0045` more than TS-DPP (standard error `0.0012`, t `3.8`), `0.0044` more than Lyapunov, and `0.0048` more than the oracle (standard error `0.0013`, t `3.7`).

Adding the same queue to Whittle reduces its cost from `0.3514` to `0.3485` and changes its penalty gap from the oracle from `-2.84` to `-2.74`; see [Baseline ordering reversed](#difference-1).

#### Conclusion

The queue reduces mean cost in this experiment. Whittle's across-instance mean is close to the budget, which does not establish budget compliance in each instance. Its penalty remains below the oracle after adding the queue, so cost differences explain only part of the penalty gap.

<a id="difference-8"></a>

### 8. Estimation bias persists and interval coverage declines

#### Difference

In replicated Fig. 7, point estimates move from the prior toward the true parameters. Repeated simulations show remaining estimation bias and declining frequency of the Beta intervals containing the truth as episodes accumulate.

#### Explanation

The paper calls the shaded band a 95% confidence interval of the Beta distribution. This replica uses the 2.5 and 97.5 percentiles of the `Beta(alpha, beta)` maintained by Eq. (14), with both estimates and intervals returned by `model.posterior_path`. These are 95% equal-tailed credible intervals of that Beta distribution: 95% denotes posterior probability mass, while frequentist coverage at a fixed `theta*` requires a separate check.

Boundary handling changes the posterior update. `simulate` zeroes `t_prev` and `s_prev` in every episode, so the first observation of a pulled arm uses truncated history. With age also reset, that observation satisfies `s <= t - 1 < n_gap = t`; Eq. (14) must record `I = 1` and increment `beta` by the observed age. With age carried, an age exceeding the elapsed episode time gives `I = 0`; because `s_prev = 0`, the entire carried age enters `beta`. This changes both the first observation's success indicator and its failure count.

#### Tests

`python src/diagnose.py fig7` fixes three `theta*` values, runs 300 simulations, and counts the frequency of the interval containing the truth (`results/fig7_calibration.csv`). The table uses `reset`, as does `posterior_path` when drawing the figure:

| Episode | `theta* = 0.239` | `0.489` | `0.839` |
| --- | --- | --- | --- |
| 20 | 86.3% | 91.7% | 94.0% |
| 50 | 74.3% | 84.3% | 92.0% |
| 100 | 65.7% | 77.7% | 81.0% |

From episode 20 to 100, mean interval widths shrink by `28%` to `34%`. RMSE falls by only `4.5%` and `6.1%` at `theta* = 0.239` and `0.839`. At `0.489`, RMSE falls by `46%` and interval width by `34%`, yet coverage falls by `14` percentage points. Relative changes in width and RMSE alone do not explain coverage.

The single trajectory in replicated Fig. 7(b) also misses the truth: `ci_low` is `0.5117` at episode 20 and `0.5095` at episode 100, both above `theta* = 0.489` (`results/estimates.csv`).

Mean estimation biases at episode 100 are `+0.045`, `+0.012`, and `-0.025`, about `4` to `10` standard errors. `python src/diagnose.py eq14` substitutes round-robin pulls to remove the influence of the arm-selection rule (`results/eq14.csv`). At `theta = 0.239`, bias is `+0.0397` after 6,400 pulls per arm (standard error `0.0006`) and `+0.0396` after 25,600 (standard error `0.0002`). Quadrupling pulls leaves the bias nearly unchanged, while `bias × pulls` rises from `253.8` to `1014.3`. Bias persists at the other two parameters as well.

The analytic check at a fixed gap `g` gives these expected increments:

```text
E[Δalpha]        = 1 - (1 - theta)^g
E[Δalpha+Δbeta]  = sum_{s<g} (1 + s) theta (1 - theta)^s
                  + g (1 - theta)^g
E[Δalpha] / E[Δalpha+Δbeta] = theta
```

The numerical residual in the last identity is at most `3e-17` for all tested `g` and `theta`. This ratio-of-expected-increments identity does not establish that the finite-sample posterior mean is unbiased.

In the paired boundary check, switching from `reset` to `carry` changes the bias at `theta = 0.239` from about `+0.042` to `-0.023`. Over 100 episodes with the same seed, `reset` gives the first arm `56` more in `alpha` and `211` less in `beta` than `carry`; the mean differences over 20 seeds are `59` and `238`. In this round-robin diagnostic, every arm has one first observation per episode, giving `N` boundary-first observations per `L` pulls. Adding episodes does not reduce this fraction.

#### Conclusion

These checks show persistent estimation bias alongside boundary history resets in this implementation, with frequentist coverage declining as the intervals narrow. Round-robin diagnostics find bias under both `reset` and `carry`, in opposite directions. The paper does not specify the boundary handling for its Fig. 7, so the available evidence does not identify which convention that figure uses.
