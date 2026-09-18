# TS-DPP Replica: Age-of-Information-Aware Mobile Crowdsensing for Uncertain Event Capture

English | [中文](README.zh.md)

> Developed and tested on Apple M4, macOS 26.2 (25C56), Python 3.13.5.

## Overview

A replication of the experiments in the following paper:

```
@inproceedings{zhou2026age,
  title={Age-of-Information-Aware Mobile Crowdsensing for Uncertain Event Capture},
  author={Zhou, Jinrui and Xu, Yin and Xu, Haotian and Xiao, Mingjun and Wu, Jie},
  booktitle={IEEE INFOCOM 2026 - IEEE Conference on Computer Communications},
  pages={1--10},
  year={2026},
  organization={IEEE},
  doi={10.1109/INFOCOM59046.2026.11571737}
}
```

The paper models uncertain event capture as a constrained episodic restless bandit with an
unknown transition probability, and proposes **TS-DPP**: a belief-Drift-Plus-Penalty bandit
policy combined with Thompson sampling.

All parameters are taken verbatim: `theta_i ~ U[0,1]`, `gamma ~ Dirichlet` with `sum gamma = 1`,
`c_i ~ U[0.2, 0.5]`, `B = 0.35`, and the Section V-A-2 baselines. The paper runs `m = 50`
episodes for the synthetic setting; this replica simulates 100 and stores every episode, so
`draw.py` draws the paper's 0..50 window from the same CSV. See Difference 4.

```
pip install numpy scipy matplotlib markovianbandit-pkg numba
python src/run.py all          # simulations  -> results/*.csv
python src/plot/draw.py        # results/*.csv -> figs/*.png
python src/diagnose.py gaps    # the evidence behind "Differences" below
python src/diagnose.py whittle # why the Whittle baseline lands below the oracle
```

`markovianbandit-pkg` declares no dependencies in its metadata but imports `numba` and
`scipy` at load time, so those must be installed explicitly.

Fig. 5 additionally needs the real-world trace, which this repository keeps reduced to
`data/2019-Dec-3types.npz` (0.8 MB: three per-second event bitmaps). `run.py all` uses that
file as is. To rebuild it from the source dataset, see Difference 6.

## Experimental Results

Fig. 3 replication: episodic penalty trends, `N = 4`.

![Fig. 3](figs/fig3.png)

Fig. 4 replication: episodic penalty trends, `N = 8`.

![Fig. 4](figs/fig4.png)

Fig. 5 replication: the real-world setting.

![Fig. 5](figs/fig5.png)

Fig. 6 replication: time-averaged regret. Fig. 7 replication: parameter estimate trends.

![Fig. 6](figs/fig6.png)
![Fig. 7](figs/fig7.png)

| Figure | Outcome |
| --- | --- |
| Fig. 3, Fig. 4 | Curves and shapes reproduced; baseline ordering is not, see Difference 1 |
| Fig. 5 | Reproduced from the paper's own slice of the trace; episode 1 is shallower, see Difference 6 |
| Fig. 6 | Decay rate reproduced; the ordinate is a different quantity, see Difference 5 |
| Fig. 7 | Trends reproduced; the shaded band is narrower than 95% coverage, see Difference 8 |

## Differences from the paper

This replica follows the paper's stated settings as closely as the text allows. The paper
releases no code, no artifact, and no pseudocode for its baselines, so the text leaves a
few implementation choices open. Each item below states the ambiguity, the choice made
here, and what that choice changes.

Every simulation runs all baselines in the paper's own online setting rather than in the
known-dynamics setting their own papers assume. All four policies therefore share one
posterior, the three queue-carrying policies share one virtual queue, and three of them
share one arm-selection rule:

| Policy | `theta` used | arm-selection rule |
| --- | --- | --- |
| Belief-DPP (oracle) | `theta*` | Eq. (13) |
| TS-DPP | one draw from the Beta posterior per episode | Eq. (13) |
| Lyapunov [20] | posterior mean | Eq. (13) — the same rule |
| Whittle [24] | posterior mean | the two-dimensional index of Difference 2, `argmax gamma_i * I_i(x, y)` |

This is the most generous reading of the baselines and the least favourable to the paper:
the paper's own criticism of this prior work is that it assumes known dynamics, known
states, or no cost constraint, and none of those handicaps survive here. What is left is
policy structure, which is what Difference 1 turns on.

### 1. The baseline ordering in Fig. 3 and Fig. 4 is inverted

This is the only difference that touches a claim rather than a rendering detail. Part of it is
not a claim about policy structure at all: the Whittle entry is the one that follows the
episode-boundary choice of Difference 6, lowest under `reset` and highest under `carry`, so
read that difference alongside this one.

The paper's Fig. 3 and Fig. 4 show, in every panel:

```
TS-DPP ~ Belief-DPP (oracle)  <  Lyapunov [20]  <  Whittle [24]
```

Reading the published panels against their own tick marks at `L = 20, V = 0.2` gives the
gaps below, at both arm counts (`python scripts/measure_fig_levels.py`). This replica gives:

| Policy | Paper, Fig. 3(a) `N = 4` | Paper, Fig. 4(a) `N = 8` | This replica (paired gap, 200 runs) |
| --- | --- | --- | --- |
| Lyapunov | `+1.71` | `+2.69` | `+0.42` (se 0.09) |
| Whittle | `+4.45` | `+8.40` | `-2.84` (se 0.25) |
| TS-DPP | `+0.01` | `+0.14` | `-0.25` (se 0.51) |

Only the Lyapunov entry agrees with the paper in sign: Lyapunov lands above the oracle.
TS-DPP lands within half a standard error of the oracle, on either side of it, so its sign
here is noise and the paper's `+0.01` is not contradicted either way. The Lyapunov gap is
about four times smaller here than the published one, which is Difference 3. The Whittle
entry is inverted, and it holds in all eight cells (paired gap `-2.8` to `-4.7`, 200 runs
each), so it is not noise.

**The index is the whole explanation.** `python src/diagnose.py whittle` rules out the two
other suspects by turning them off one at a time:

| Variant | Tail penalty | vs. TS-DPP | vs. oracle | Realised cost |
| --- | --- | --- | --- | --- |
| Belief-DPP (oracle), `theta*` known | `77.21` | `-0.42` (se 0.09) | `+0.00` | `0.3467` |
| TS-DPP | `77.63` | `+0.00` | `+0.42` (se 0.09) | `0.3471` |
| Whittle index, no budget term | `74.37` | `-3.26` (se 0.25) | `-2.84` (se 0.25) | `0.3514` |
| Whittle index + Eq. (12) queue | `74.47` | `-3.16` (se 0.25) | `-2.74` (se 0.25) | `0.3485` |
| Whittle index + queue, `theta*` known | `74.57` | `-3.06` (se 0.28) | `-2.64` (se 0.27) | `0.3484` |

Extra spend is not the explanation: giving the Whittle policy the same virtual queue pulls
its cost back down to everyone else's level and leaves `-2.74` of the `-2.84` standing.
Neither is knowing `theta*`. What remains is the policy structure, and there is a real
reason for it: the paper's oracle is not an optimal policy. It is the drift-plus-penalty
rule of Eq. (13) with the state known — optimal *within the DPP family*, not over all
policies. The Whittle index solves the average-reward relaxed problem, and on this arm it
finds a better schedule than Eq. (13) does. A learned policy beating a known-state policy
is only a contradiction if the known-state policy is optimal.

The paper's Fig. 3 could still be right about its own Whittle baseline, because its
baseline is probably not this index — see Difference 2.

### 2. The Whittle baseline is ambiguous, and the published index does not transfer

The paper cites [24] (Hsu, Modiano, Duan), whose index is closed-form:

```
I(x) = x^2/2 - x/2 + x/p
```

*Hsu, ISIT 2017, Thm. 7; extended in IEEE TMC 19(12), 2019, Thm. 17.*

It is derived for a subproblem in which serving an arm resets that arm's age to `1`. Here,
pulling PoI `a` instead sets `Y_a := X_a + 1` (Eq. 4) — it installs whatever event is
currently on record, which may be stale. The two subproblems are not isomorphic, and the
formula points the wrong way: it chases the stalest event.

`python src/diagnose.py variants` tests this directly. Every variant shares the same seeds
and is compared against the oracle in the same rollout:

| Variant | Paired gap vs. oracle | Verdict |
| --- | --- | --- |
| Hsu's closed form, belief state | `+70.7` (se 2.7) | worse than oracle |
| Hsu's closed form, observed copy age | `+17.9` (se 1.6) | worse than oracle |
| Index derived for this model's 2-D arm | `-2.84` (se 0.25) | better than oracle |

Applying Hsu's formula verbatim reproduces the *direction* of the paper's ordering — the
Whittle curve lands clearly above the oracle, as in the published figure. Deriving the
index for this model's actual arm reverses it. This replica uses the derived index, so the
Whittle curve here is expected to differ from the paper's.

The arm is two-dimensional, `(event age x, copy age y)`, precisely because a pull installs
`X + 1` rather than resetting to `1`. `src/sim/whittle.py` builds that arm and hands
the subsidy bisection to `markovianbandit-pkg`.

### 3. The Lyapunov baseline is under-specified, and Eq. (13) already is the DPP rule

[20]'s printed index divides by `(1 + phi_n(alpha) / lambda_n)`. The arms here carry no
frame length or idle parameter, so this replica uses the un-normalised numerator.

More importantly, Eq. (13) of the paper *is* the drift-plus-penalty rule for the quadratic
Lyapunov function `L(Z) = Z^2 / 2`, reduced to a per-arm closed form. A faithful
implementation of [20] is therefore bound to tie the oracle rather than lose to it, and it
does: `+0.42` (se 0.09).

Producing the paper's `+2` gap requires indexing the observable copy age instead of the
Eq. (16) belief, but that variant lands at `+43.9` (se 1.8), overshooting by an order of
magnitude. We could not find a variant that reproduces both the direction and the
magnitude of the paper's Lyapunov gap. This one is unresolved.

### 4. The plotted levels differ; the `N`-scaling does not

The two panels do not share a y-axis: Fig. 3(a) spans `65.6` to `78.8` and Fig. 4(a) spans
`86.5` to `103.2`. Reading them against their own tick marks rather than by eye therefore
matters, and `python scripts/measure_fig_levels.py` does that reading:

| | Fig. 3(a), `N = 4` | Fig. 4(a), `N = 8` | ratio |
| --- | --- | --- | --- |
| Paper, Belief-DPP (oracle) | `66.74` | `87.89` | `1.32` |
| This replica, oracle (median) | `70.44` | `92.12` | `1.31` |
| This replica, oracle (mean) | `76.05` | `95.48` | `1.26` |

The replica's rows are the oracle entries of `results/penalty_tails.csv`. The scaling
agrees; the level does not. The paper's penalty rises by `1.32` between `N = 4` and `N = 8`,
and this replica's rises by `1.31` on the medians -- a gap of `0.01`, an order of magnitude
below the `2.0`-unit tick spacing of the panel it was read from. What is left is a level
offset: `9.3` units at `N = 4` and `7.6` at `N = 8` against the means, or `3.7` and `4.2`
against the medians.

Which of those two rows to compare against is not a detail, because the paper's plotted
level is itself a mean over an unstated number of runs, and this replica's own mean and
median are `5.6` units apart (se `1.1`) at `N = 4`. The likely cause of that spread is
heavy tails rather than a modelling error. With `theta ~ U[0,1]`, the mean event age
`E[(1 - theta) / theta]` diverges, so a cross-run mean is dominated by the rare arms with a
very small `theta`. The paper states `m = 50` episodes but not how many independent draws
of `theta*` were averaged, so the two means are not estimating the same finite quantity
with the same precision, and an offset of this size cannot be attributed to the replica.

A penalty that doubled between `N = 4` and `N = 8` would sit at `133` in Fig. 4(a), above
that panel's own axis maximum of `103.2`. The penalty is `sum_i gamma_i Y_i` with
`sum_i gamma_i = 1`, so it averages over arms rather than accumulating across them, and
nothing in the model or in the paper's own bounds scales it by `N`.

The paper stops Fig. 3 and Fig. 4 at episode 50 because its synthetic runs are `m = 50`.
`src/plot/draw.py` draws that same 0..50 window. The CSV behind it holds 100 episodes --
the length Fig. 6 and Fig. 7 use -- so moving the window is a change to `HORIZON` alone,
with no re-simulation.

### 5. "Time-averaged regret" is undefined, so the two ordinates are not the same quantity

Fig. 6 plots a quantity the paper calls the time-averaged regret without defining the
normalisation, and no normalisation fits both Fig. 5 and Fig. 6. The paper's Fig. 5 shows
real-world episodic penalties of roughly 60 to 200 at `N = 3, L = 20` — the lowest
first-episode point across its four panels is `63.2` and the highest plateau is `190.3`
(`python scripts/measure_fig_levels.py`) — so one whole episode costs at most about 200.
Fig. 6 nevertheless opens far higher: at episode 1 its five curves sit between `2264` and
`3925`, the top of that range being the theorem's upper bound and the other four TS-DPP at
`V = 0.5, 1, 5, 10` (`python scripts/measure_fig_levels.py`; the panel's legend labels two
different curves `L = 20, V = 0.5`, so the dashed one is identified as the bound from the
paper's text, which contrasts the regret against "the upper bound we established"). Read as
a per-episode regret, episode 1 would be `11` to `20` times the total penalty of an entire
episode; read as a per-slot average, `226` to `392` times a per-slot penalty of `10`. Either
way the constant is not one that Fig. 5 supports, and the paper does not state what it is.

This replica plots the running mean of the per-episode Bayesian regret,

```
Delta_l          = E_{theta*}[ pen_l(policy) ] - E_{theta*}[ pen_l(oracle) ]
time-averaged(l) = (1/l) * sum_{j<=l} Delta_j
```

with the Theorem 2 bound scaled to share the episode-1 anchor, since the paper's bound
carries an unspecified constant. Only the decay-rate comparison is meaningful, and it does
hold: the empirical curve is down to `0.53` by episode 100, where the bound is `2.3x` higher
(`2.8x` at its widest).
For the same reason the four `V` curves coincide here: the regret is dominated by the
estimation error, and `V` moves the endpoint by under 6 percent (`0.535` at `V = 0.5`
against `0.563` at `V = 1`). They do *not* coincide in the paper, which is the same
ambiguity seen from the other side: its four TS-DPP curves start between `2264` and `3578`
and settle between `19` and `116`, a factor of six, on a figure whose text reports all four
as converging. A regret measured against the `V`-optimal policy rather than against this
replica's oracle would move with `V` exactly as those panels do. The paper does not say which
reference it uses, so the coincidence here is not evidence against it — but it does mean the
two figures are not plotting the same quantity, which is what this difference is about.

### 6. Fig. 5's slice of the trace is inferred from the paper's own count

The paper assigns the two settings explicitly, so there is no guesswork about which figure
uses which: "In the synthetic experiments, we display the episodic penalty trends ... as
illustrated in Fig. 3 and Fig. 4", and "we evaluate its performance on a real-world dataset
under varying values of the hyperparameter `V ∈ {0.04, 0.06, 0.08, 0.10}`. As illustrated in
Fig. 5". Fig. 3, Fig. 4 and Fig. 6 use the synthetic setting; Fig. 5 uses the trace.

Reference [31] gives the Kaggle URL and nothing else — no month, no file, no version. The
download is not the obstacle; it needs no account:

```
curl -L -o cosmetics.zip \
  "https://www.kaggle.com/api/v1/datasets/download/mkechinov/ecommerce-events-history-in-cosmetics-shop"
unzip -d cosmetics cosmetics.zip                        # five monthly CSVs, 2019-Oct to 2020-Feb
python src/sim/extract.py cosmetics/2019-Dec.csv.gz     # -> data/2019-Dec-3types.npz
```

The paper says it excludes "one type of infrequent event", keeps the other three, and counts
1,654,771 occurrences. That number is a count of *occupied 1-second slots*, not of rows: the
paper maps every timestamp to a uniform 1-second slot and calls the slot the event's actual
occurrence time, so events sharing a second collapse to one. Counting rows, occupied slots,
distinct users and distinct `(user, item)` pairs over every monthly file and every two-,
three- and four-type subset of its four event types, one slice lands within 0.5 percent:

| Slice | Count | Off by | Relative |
| --- | --- | --- | --- |
| 2019-Dec `view` + `cart` + `remove_from_cart`, occupied slots | 1,647,519 | −7,252 | −0.44% |
| 2019-Oct `view` + `cart` + `purchase`, occupied slots | 1,645,164 | −9,607 | −0.58% |
| 2020-Jan `view` + `purchase`, distinct `(user, item)` | 1,662,767 | +7,996 | +0.48% |
| 2019-Dec `cart` + `remove_from_cart` + `purchase`, rows | 1,804,955 | +150,184 | +9.1% |

The first row is the one the description fits. `purchase` is the infrequent type — 29,137
occupied seconds in December against 422,184 or more for each of the other three — and
December is the only month whose three frequent types are small enough; the other four give
1,717,728 or more. The residual 0.44 percent is most likely a different snapshot: all five
files in the current dataset are dated 2020-03-16, and Kaggle datasets can be replaced in
place.

Only the first row of that table can be checked from this repository:
`data/2019-Dec-3types.npz` carries exactly those three types, and a reader can recount its
occupied slots. The other three rows, the `29,137` for `purchase`, the `1,717,728` for the
other months, and the file dates need the raw monthly CSVs, which are not committed here —
they rest on a reading taken once and are marked as such rather than presented as
reproducible.

`theta` comes from the trace and only from the trace — `view` 0.4391, `cart` 0.2702,
`remove_from_cart` 0.1576 occupied slots per second. `gamma`, `c` and `B` keep the
configuration Section V-A-1 states applies to "all simulations" (Dirichlet with `sum gamma = 1`,
`U[0.2, 0.5]`, `0.35`). Events are replayed from the trace rather than resampled from
`Bernoulli(theta_hat)`: the Bernoulli description is given for the synthetic setting only, and
a rate fit would throw away the burstiness that is the reason to use a real trace at all.
Replay also lands closer to the paper's level than resampling does. The paper does not say how
many runs Fig. 5 averages; it states a Monte Carlo sample size of 1000 once, for Fig. 6, and
this replica uses 1000 for Fig. 5 as well, redrawing the instance per run and simulating all
four `V` on the same draw so the panels stay paired.

**The episode boundary decides both the shape and the level of Fig. 5.** The paper does not
say whether the AoI state `X, Y` survives the boundary between episodes, and it is the one
choice that turns a flat line into the paper's. Same trace, same `theta_hat`, same everything
else. The rows are the oracle, which isolates the effect -- it knows `theta*` and does not
learn, so nothing but the warm-up moves:

| `X, Y` at the episode boundary | episode 1 | episode 5 | plateau | ep1 / plateau |
| --- | --- | --- | --- | --- |
| reset to 0 | 96.9 | 98.2 | 98.7 | 0.981 |
| carried over | 96.9 | 151.1 | 154.6 | 0.627 |
| paper, Fig. 5(b), TS-DPP | `63.2` | `124.5` | `145.9` | `0.43` |
| paper, Fig. 5(b), Lyapunov | `69.9` | `133.3` | `155.5` | `0.45` |
| paper, Fig. 5(b), Whittle | `83.0` | `150.1` | `173.2` | `0.48` |

The table's rows are `V = 0.06`, the paper's Fig. 5(b), from `python src/diagnose.py carry`,
which prints every `V`. The first two rows are the oracle, which the paper's Fig. 5 does not
draw: it is there to isolate the warm-up, since it knows `theta*` and does not learn. The
last three rows are the paper's own three curves, read off its raster tick marks by
`python scripts/measure_fig_levels.py`.

The virtual queue is not part of that choice. Eq. (7) averages the realised cost over one
episode of length `L`, so `Z` is re-zeroed at the top of every episode in both rows. Carrying
`Z` as well makes it diverge instead: the constraint never stops biting, `Z` grows without
bound, and at `V = 0.06` the penalty climbs to `321` by episode 100 and is still climbing.
Whittle, which has no `Z` at all, is the
only policy that stays bounded under a carried `Z`. `simulate` takes a `carry` flag and it
carries `X, Y` only.

Carrying `X, Y` also closes the level gap, and it does so on the December slice's own
`theta_hat = (0.4391, 0.2702, 0.1576)` — the event rate needs no correction. Compared like
policy against the paper's own curves at `V = 0.06`, the plateaus line up: Lyapunov `154.4`
against `155.5`, TS-DPP `155.4` against `145.9`, Whittle `188.0` against `173.2`
(`results/realworld_curves.csv`). Reset, the oracle's plateau is 99, and the whole of that
deficit is the per-episode warm-up rather than anything about the data.

**The same flag would fix Fig. 3 and Fig. 4's ordering and breaks their shape.** Under `carry`
the synthetic curves rise too, `N = 4, L = 20, V = 0.2` giving `ep1 / plateau` of 0.57 for the
oracle and 0.57 for TS-DPP, where the paper's fall. Under `reset` those two figures come out
right and Fig. 5 does not. No single setting produces both, so this replica carries for the
trace and resets for the synthetic curves: the synthetic setting draws a fresh `theta*` per
run, so one episode is one experiment, while the trace has no boundary in it at all.
Whittle's ordering follows the same flag — lowest under `reset`, highest under `carry` — so
the inversion in Difference 1 is at least partly this choice rather than a difference in
policy structure.

**Two residuals remain.** The depth of episode 1: this replica's TS-DPP opens at `0.67` of
its plateau, the paper's at `0.43`; Lyapunov at `0.65` against `0.45`. The recovery is faster
too — by episode 5 this replica's TS-DPP and Lyapunov sit at `1.02` and `0.98` of their
plateaus, the paper's at `0.85` and `0.86`. Both follow from how much age a 20-slot episode
has to rebuild, which depends on where in the trace the window lands, and the paper does not
say how it picks windows. The other is the 0.44 percent count gap in the slice table above.

Whittle's ordering matches the paper here, highest in all four panels, unlike in Fig. 3 and
Fig. 4. Difference 1 applies to those two only.

### 7. The budget constraint only bites on the policies that respect it

The paper sets `B` equal to the expected cost of uniformly random arm selection, and the
uniform draw of `c_i ~ U[0.2, 0.5]` delivers exactly `0.35`. Any policy that is indifferent
to price therefore meets the constraint automatically. What the constraint actually does is
push the policies that *do* carry a virtual queue to spend less than they otherwise would.

Pooled over the same 200 instances per policy (`python src/diagnose.py cost`), the realised
costs separate cleanly:

| Policy | Realised cost | se | `(mean − B) / se` |
| --- | --- | --- | --- |
| Belief-DPP (oracle) | `0.3467` | `0.0036` | `-0.9` |
| TS-DPP | `0.3469` | `0.0036` | `-0.9` |
| Lyapunov [20] | `0.3471` | `0.0036` | `-0.8` |
| Whittle [24], no queue | `0.3514` | `0.0035` | `+0.4` |

Whittle, which carries no queue because [24] prescribes no budget control, sits at `B` with
a t-statistic of `+0.4` — it is not overspending, and it is not the constraint that
separates it from the others. The three queue-carrying policies are the ones behaving
oddly: their queues drive them `0.8` to `0.9` percent *under* the budget. Paired on the same
instances (`results/cost_paired.csv`), Whittle spends `0.0045` more than TS-DPP (se `0.0012`,
t `3.8`), `0.0044` more than Lyapunov, and `0.0048` more than the oracle (se `0.0013`,
t `3.7`).

So the constraint is not slack so much as one-sided: it costs the DPP policies penalty and
costs a queue-free policy nothing. That is the second half of Difference 1 — restoring the
queue to Whittle brings its cost down from `0.3514` to `0.3485` and leaves `-2.74` of its
`-2.84` penalty advantage standing.

### 8. Fig. 7's band is not a 95% interval

The paper says the shaded regions of Fig. 7 "indicate the 95% confidence intervals of the
beta distribution", and this replica draws exactly those: the 2.5 and 97.5 percentiles of
the `Beta(alpha, beta)` that Eq. (14) maintains, from the same `model.posterior_path` call
the figure is drawn from. The point estimates behave as the text describes -- they start
near the prior and settle near `theta*`. The coverage does not. `python src/diagnose.py
fig7` runs 300 realisations and counts how often the band contains `theta*`:

| episodes | `theta* = 0.239` | `0.489` | `0.839` |
| --- | --- | --- | --- |
| 20 | 86.3% | 91.7% | 94.0% |
| 50 | 74.3% | 84.3% | 92.0% |
| 100 | 65.7% | 77.7% | 81.0% |

Coverage falls as episodes accumulate. The band's mean width narrows over the same span by
`28` to `34` percent at each of the three `theta*`, while the RMSE at `0.239` and `0.839`
falls by only `4.5` and `6.1` percent -- there the interval tightens around an estimate that
is not improving. At `0.489` the RMSE falls further than the band does, `46` against `34`
percent, and coverage drops by `14` points anyway, which points at the estimate rather than
at the band.

The figure's own realisation shows it. In panel (b) the band sits entirely *above* the true
value from the first checkpoint on: `ci_low` is `0.5117` at episode 20 and `0.5095` at
episode 100, against `theta* = 0.489` (`results/estimates.csv`, the data behind
`figs/fig7.png`). A reader who checks that panel against its red line is looking at an
interval that misses, not one that is merely narrow.

The estimate also stays biased toward the middle: small `theta*` is over-estimated and
large `theta*` under-estimated, by `+0.045`, `+0.012` and `-0.025` at episode 100, each
between 4 and 10 standard errors. That bias does not decay. With the policy removed and a
round-robin pull substituted so that only Eq. (14) is under test, it is still `+0.0397` at
`theta = 0.239` after 6,400 pulls (se `0.0006`), and `+0.0396` after 25,600 (se `0.0002`) —
flat over a quadrupling of the sample, with `bias x pulls` rising `253.8` to `1014.3` over
that range instead of levelling. The two other `theta` behave the same way (`python src/diagnose.py eq14`).

Eq. (14) is not what produces it. When each pull of an arm comes exactly `g` slots after the
previous one, the update is unbiased: its per-pull expectation of `alpha` is
`1 - (1 - theta)^g` and of `beta` is `sum_{s<g} (1 + s) theta (1 - theta)^s + g
(1 - theta)^g`, and their ratio is `theta` to within `3e-17` for every `g` and `theta` tried
(`python src/diagnose.py eq14`).

The bias lives at the episode boundary. `simulate` re-zeroes the clock `t_prev` and the
previous age `s_prev` at every boundary, so the first pull of each arm in each episode is
scored against a history the boundary just truncated. With the age reset as well, the
observed age is at most `t - 1` against an `n_gap` of `t`, so Eq. (14) is *forced* to
`I = 1`: a success booked with almost no failures. Carrying the age instead hands Eq. (14) the true carried age, which
usually exceeds the truncated clock, so it books `I = 0` and charges `beta` the whole
carried age as a run of failures. That is the direction the measured bias moves, `+0.042` to
`-0.023` at `theta = 0.239`; over 100 episodes and one seed the first arm books `alpha` `56`
higher and `beta` `211` lower under the reset, `59` and `238` averaged over 20 seeds.

The paper does not say which convention its Fig. 7 uses, and both are biased -- the reset
inflates the estimate, the carry deflates it -- so the coverage table above is not an
artifact of picking the wrong one. The numbers are the reset convention, which is the one
`posterior_path` draws the figure with.

Those forged successes arrive at a fixed rate -- one per episode per arm, so `N` of them out
of every `L` pulls -- and that is why the bias does not decay with more data. An episode
boundary re-forges the same one-sided reading every time, so the contamination is a constant
*fraction* of the sample rather than a vanishing one, and adding episodes adds biased and
unbiased pulls in the same proportion.

## Issues

For bugs, questions, or discussions, please use the issues section of this repository.

## Contributions

We welcome contributions to enhance the accuracy of replication. Fork the repository,
commit your changes, and make a pull request.
