# DESIGN — Lean 4 formalization of *Age-of-Information-Aware Mobile Crowdsensing for Uncertain Event Capture* (INFOCOM'26)

Paper: `infocom26.pdf` (Zhou, Xu, Xu, Xiao, Wu).
Dependencies permitted: `ref.txt` (Lean install docs + LML, rl-theory-in-lean, lean-stat-learning-theory,
FormalSLT, FormalML, mathlib4). **Of these, only the last two are actually used**: `mathlib4` is the
sole `[[require]]` in `lean4/lakefile.toml` and the sole external import anywhere in the tree
(`grep -rh '^import' lean4/TSDPP/*.lean lean4/TSDPP.lean` yields only `Mathlib` and `TSDPP.*`). The
five ML/SLT repositories are **permitted but unused** — no clone, no Lake dependency, no import;
they are listed because `ref.txt` allows them, not because the development rests on them. This
matters for how the artifact should be read: nothing below is borrowed from them, and the one place
a result of theirs would have helped (GAP-7's trajectory law) is instead taken from the vendored
mathlib (`Probability/Kernel/IonescuTulcea/Traj.lean`) — that is API lookup, not citation.
Toolchain: Lean `v4.35.0-rc2`, mathlib4 `f61f3ed7633ff99ecaae4a086395b501652a76ee`, project at `lean4/`.

Hard constraints (from `CLAUDE.md`):
no `sorry`, no new axioms, no `native_decide`, no `unsafe`, no floats, no `admit`.
Core argument derived from first principles; literature used **only** to look up API, never to justify a step.

---

## 1. `<ROOT_STATEMENT>`

The paper's headline theoretical claim is **Theorem 2** (§IV, Eq (19)):

> The Bayesian regret of the TS-DPP algorithm satisfies
> `BR(T) = O( √(L³ · T · log T) )`,
> where `BR(T)` is Eq (18), `T = m·L` is the horizon, `L` the episode length.

Supporting named results in the paper:

| id | paper item | statement |
|----|-----------|-----------|
| R1 | Definition 1 / Eq (2),(3) | event AoI Markov chain: reset to 0 w.p. `θ_i`, else `+1` |
| R2 | Definition 3 / Eq (4) | platform-copy AoI recursion |
| R3 | Eq (9) | per-round penalty identity, `r(t) = Σ_i γ_i Y_i(t)` |
| R4 | Eq (10),(12),(13) | cost, virtual queue `Z`, belief-DPP argmin |
| R5 | Eq (15) | exact law of `X_i(t)` given record `(λ_i, δ_i)` |
| R6 | Eq (16) | closed form of belief state `X^b_i(t)` |
| R7 | **Theorem 1** | Beta–Bernoulli conjugacy, Eq (14) posterior update |
| R8 | Lemma 1 | belief-DPP is a deterministic policy mapping |
| R9 | **Lemma 2** | Eq (23),(24): two Lipschitz bounds on the state law |
| L34 | Lemma 3, 4 | Bayesian-regret decomposition (quoted from [28]) — carried as **hypotheses** |
| L5 | Lemma 5 | Beta concentration inequality (quoted from [45]) — carried as **hypotheses**.  **Defective as used: see P-64** — the paper states it for `0 ≤ r ≤ 1` (true) and applies it at `r = max{1, √(8 log T/α)} ≥ 1` (false, exact counterexample), and the artifact inherited the inverted range |
| R12 | Lemma 6, Cor. 1 | state bound `X_i(t) ≤ D`, `α^l_i ≥ η l` |
| R13 | Eq (36),(37) | per-round parameter-perturbation budget |
| R14 | Eq (38)–(40) | finite-sum assembly to the big-O |

Note the card ids in `cards/` are finer-grained than the paper's item names: `cards/R10.md`
is Eq (36)+(37), `cards/R11.md` is Eq (38), `cards/R13.md` is Eq (40), `cards/R14.md` is Eq (39),
`cards/R16.md` is the final arithmetic, and `cards/R17.md` is the assembled Theorem 2.  The two
citation nodes are `L34` and `L5` in every document, to keep them visibly distinct from the
cards that *use* them.

**Deliverable**: a sorry-free, axiom-free Lean 4 development that machine-checks every item above that is
mathematically closable *as written*, plus a precise, itemized statement of which items are not, and why.

## 2. Verification protocol

Two independent deliverables, each verified separately, exactly as `CLAUDE.md` demands:

* **(A) informal proof** — §3 below, the mathematical argument, checked against the paper's claims by
  hand and by independent numeric falsification (`scripts/numeric_check.py`).
* **(B) formal artifact** — `lean4/TSDPP/*.lean`, checked by `lake build` and by a `#print axioms`
  audit asserting every headline theorem depends only on
  `propext`, `Classical.choice`, `Quot.sound`.

  > **Documentation correction.** Earlier revisions of this line claimed the build was run "with
  > `set_option autoImplicit false`". **That was false** — `grep -rn autoImplicit lean4/TSDPP/
  > lean4/TSDPP.lean lean4/lakefile.toml` returns nothing, and `autoImplicit` defaults to `true` in
  > Lean 4. The claim has been removed rather than left standing. Enabling it is *known feasible*
  > (`lake env lean -DautoImplicit=false` succeeds on `TSDPP/Basic.lean`, `TSDPP/Lipschitz.lean`
  > and `TSDPP/Theorem2.lean`, the three spot-checked), but it has **not** been enabled project-wide,
  > so it is not claimed here. Recorded as a verified-possible hardening of the gate, not as a
  > property of the delivered artifact. (Same class of defect as the stale audit count below:
  > a design document asserting a verification that the toolchain was never asked to perform.)

A claim is only reported as closed when *both* pass. Numeric checks are **falsifiers, not proofs** —
they are recorded because two of them changed the plan (see §6, traps P-3, P-4).

## 3. Card DAG

Each node = a theorem card `cards/<id>.md`.  Edge `X → Y` means *Y is proved from X*.
A card is `CLOSED` only when its Lean declaration builds with no `sorry` and the
`#print axioms` audit (§2 B) comes back clean.  **The status board below is regenerated from
`lake build` output, never hand-edited.**

```
R1 (AoI chain, Eq 2-3)          ──────────────┐
                                              ├──► R12a (Lemma 6, tail_le_eps)
R2 (copy AoI, Eq 4)             ──────────────┘
        │
        └──► R5 (Eq 15 law) ──► R6 (Eq 16 mean) ──┐
                     │                            │
                     └──► R9 (Lemma 2) ───────────┤
                              │  ▲                │
R8 (Lemma 1 det. policy) ─────┘  │                ├──► R10 (Eq 36, 37) ──┐
                                 │                │                       │
R3 (Eq 9 penalty) ──► R15 (Eq 35)┘                │                       ├──► R16
                                                  │                       │   (final rate)
R7 (Theorem 1 conjugacy, Beta) ───────────────────┘                       │
                                                                          │
R14 (Eq 39, finite-sum) ──────────────────────────────────────────────────┤
                                                                          │
R13 (Eq 40, geometric tail) ──────────────────────────────────────────────┘
                                                                            │
                                                                            ▼
                                                                         ROOT
                                                             (Theorem 2, O(√(L³T log T)))

Citation boundary (NOT closed by proof, carried as explicit hypotheses; see §7):
  R10' = Lemma 3 + Lemma 4  (regret decomposition, quoted from [28])
  R11' = Lemma 5            (Beta concentration, quoted from [45])
```

### Status board (verified against `lake build` + `scripts/check_axioms.sh`)

Every CLOSED row is backed by a declaration that (a) is in the `TSDPP` root module's import
closure, (b) contains no `sorry`/`admit`/`native_decide`/`unsafe`, and (c) whose `#print axioms`
output is a subset of `{propext, Classical.choice, Quot.sound}`.  The last point is *enforced*, not
asserted: `lean4/scripts/check_axioms.sh` fails the build if any audited declaration deviates.
Last full run: **79 declarations audited (3 with an empty axiom set), 23 source files scanned, all
clean** — plus module-level coverage `21/22` in the root import closure (`TSDPP.Basic` declares
nothing and is allowlisted).  See trap P-65: the module-level coverage line is a floor, not a
statement that the closure is audited; 30 of 109 public declarations are still outside it.  (Up from 58/24 when `BetaGamma`, `BetaGammaChernoff` and `UnionBound` were brought into
the root import closure — see the import block in `TSDPP.lean`.  Those three had been *outside* it,
which meant `lake build` never compiled them and `scan_forbidden.py` never read them; the same hole
the root module's own comment had already flagged for `KL` and `GammaMGF`.)

**Tree invariant, now enforced.**  Every `TSDPP/*.lean` file must be either the root module, or
reachable from it by `import`.  A file that is in the directory but outside the closure is compiled
by nothing and, for `lake build` purposes, does not exist — this hole has now been hit four times
(`KL`/`GammaMGF`, then `BetaGamma`, then the two promoted modules, then the four quarantined
below), so it is worth stating as a rule rather than rediscovering.  The current check is one line:

```
grep "^import TSDPP" TSDPP.lean | sed 's/import TSDPP\.//' | sort > /tmp/incl
ls TSDPP/*.lean | xargs -n1 basename | sed 's/\.lean//' | sort > /tmp/all
comm -13 /tmp/incl /tmp/all      # must print nothing but the file currently in flight
```

**Four superseded modules quarantined to `Scratch/superseded/`.**  `BetaMeasureIci.lean`,
`SubstLemmas.lean`, `GammaExpIntegral.lean` and `OfRealAlgebra.lean` each declared, publicly, one or
more of the lemmas that `TSDPP/BetaGamma.lean` now carries as `private` helpers —
`betaMeasure_Ici`, `setLIntegral_of_measure_eq_zero`, `lintegral_sub_right`,
`lintegral_mul_left_of_pos`, `lintegral_rpow_exp_neg_Ioi`, `gammaPDF_mul_factor` are all present in
both places.  They were imported by **nobody** and therefore never compiled.  Verified before moving:
all four compile clean standalone, so nothing was silently broken; and all six names are
`private` in `BetaGamma.lean` (lines 9, 13, 20, 28, 95, 145), so the public copies were dead rather
than load-bearing.  They were *moved*, not deleted — they are the pre-consolidation history of the
ratio-law proof and may still be useful to a reader reconstructing it.  (The three with an *empty* axiom set are `copyStep`, `copyStep_other`, `copyStep_self` —
they depend on no axioms at all, not even `propext`; the audit checker counts verdicts, so an empty
set is a legitimate outcome it must not mistake for a missing verdict — trap P-21.)  These counts
are **regenerated from the tool, never hand-edited**; an earlier revision of this line read
"43 declarations, 13 source files" and had simply gone stale as the development grew.  The audit list is not only the headline theorems: it also carries the `FIDELITY.md` §1.0
coverage rows (Definitions 2–4, Lemma 1, and the remaining Theorem 1 forms), so that every item
that document calls *closed* is machine-checked rather than merely asserted.

| card | paper item | status | Lean declaration |
|------|-----------|--------|------------------|
| R1  | Eq (2),(3) AoI chain | CLOSED | `TSDPP.chainPMF_sum_one`, `TSDPP.chain_path_no_reset` |
| R2  | Eq (4) copy-AoI recursion | CLOSED | `TSDPP.copyStep_iterate` |
| R3  | Eq (9) penalty identity | CLOSED | `TSDPP.penalty_identity` |
| R5  | Eq (15) state law is a PMF | CLOSED | `TSDPP.pmf_sum_one` |
| R6  | Eq (16) belief-state mean | CLOSED | `TSDPP.pmf_mean` |
| R7  | **Theorem 1** Beta–Bernoulli conjugacy | CLOSED | `TSDPP.betaPDFReal_conj`, `TSDPP.lintegral_conj` |
| R8  | Lemma 1 deterministic policy mapping | CLOSED | `TSDPP.bestArm_spec`, `TSDPP.bestArm_congr` |
| R9  | **Lemma 2** Eq (23),(24),(25),(26) | CLOSED | `TSDPP.l1_lipschitz`, `TSDPP.firstMoment_lipschitz`, `TSDPP.armTerm_lipschitz`, `TSDPP.atomTerm_lipschitz` |
| R9a | Lemma 2's analytic core `sup|f'| ≤ 1` | CLOSED | `TSDPP.arm_deriv_abs_le_one` (+ `TSDPP/Ineq.lean`) |
| R12a| **Lemma 6** state tail bound | CLOSED | `TSDPP.tail_le_eps` |
| R15 | Eq (35) penalty cancellation | CLOSED | `TSDPP.penalty_diff` |
| R10a| Eq (36) per-round penalty difference | CLOSED | `TSDPP.perRoundPenaltyDiff_le` |
| R10b| Eq (37) value-function term | CLOSED | `TSDPP.stateTerm_le` |
| R11 | Eq (38) assembly over rounds/episodes | CLOSED | `TSDPP.episodeRegret_le`, `TSDPP.regret_le` |
| R14 | Eq (39) finite-sum assembly | CLOSED | `TSDPP.sum_range_inv_sqrt_le`, `TSDPP.sum_inv_sqrt_weighted` |
| R13 | Eq (40) geometric tail | CLOSED | `TSDPP.geom_exp_sum_le`, `TSDPP.tail_sum_le` |
| R16 | final-rate arithmetic `2L√(K₀Z)+B ≤ 8√(L⁴Z)`, `K₀ = 100/11` | CLOSED | `TSDPP.rate_core`, `TSDPP.regretCoeff`, `TSDPP.two_mul_sqrt_ratio_le` |
| **R17** | **Eq (19) Theorem 2, assembled (ROOT)** | **CLOSED** | **`TSDPP.theorem2_rate`, `TSDPP.theorem2_concrete`, `TSDPP.theorem2_withTail`, `TSDPP.eq39_collapse`** |
| R12b| `η > 0`, `C`, `D` as T-free constants | **GAP-3** | — (unrepairable as printed) |
| —   | exponent `L³` in Eq (19) | **GAP-4** | — (paper is internally inconsistent) |
| —   | Eq (40)'s printed constant | **GAP-6** | — (printed step is **false**; §7) |
| L34 | Lemma 3, Lemma 4 (quoted from [28]) | **hypothesis, not axiom** | `Theorem2.theorem2_concrete` takes `hdecomp`/`hper` as premises |
| L5  | Lemma 5 (quoted from [45]) | **hypothesis, not axiom** | `Theorem2.theorem2_concrete` takes `hdelta`/`hηl` as premises |

**The `O(·)` boundary.**  `theorem2_rate` proves `|BR| ≤ c·L·√(L³T log T/η)` with
`c = 8·(½C² + 2C² + 2CD + C)` explicit and `T`-free, via `theorem2_concrete` and
`regretCoeff_le_mul`.  (The `8` is the paper's `7` after the radius constant became `K₀ = 100/11`
instead of `8`; see trap P-19 and `cards/R13.md`.)  The whole *numerical* content of the paper's rate is therefore
machine-checked.  What is not formalized is the `O(·)` **symbol** itself: it needs a filter on `T`
and a decision on whether `L` grows with `T` (GAP-4), which the paper never fixes.  Choosing that
convention is a modelling decision, not a mathematical gap — `FIDELITY.md` §4 carries the
discussion.

## 4. Conventions fixed before any tactic (paper is ambiguous here)

* **Index convention (GAP-5).** Eq (4) refreshes the copy from `X_i(t−1)`, but Eq (9) prints
  `X_{A_t}(t)`. These differ by one slot. The formalization pins **Eq (4)'s** convention,
  because Eq (4) is the recursion that is actually *defined* and Eq (9)'s printed form is not
  consistent with it. Concretely, `TSDPP.penalty_identity` takes `X` to be the **pre-slot**
  event AoI `X_i(t−1)` and `Y` the pre-slot copy AoI `Y_i(t−1)`, and proves
  `Σ_i γ_i·(if i = a then X_i + 1 else Y_i + 1) = Σ_i γ_i Y_i + 1 + γ_a(X_a − Y_a)`.
  The off-by-one cancels in Eq (35) because both sides of the subtracted expectations use the
  same convention, so `TSDPP.penalty_diff` is unaffected. Recorded as GAP-5 in §7.
* **Support.** `X_i(t)` ranges over `ℕ`; all sums are over `Finset.range (λ+δ+1)`, which provably
  contains the support, rather than a bespoke support set (trap P-5).
* **θ ∈ (0,1).** Eq (16) divides by `θ`. `Belief.pmf_mean` is proved for `θ ≠ 0`; the `θ = 0` case
  is degenerate (the chain is absorbed at `∞` with weight `0`) and is not claimed. By contrast
  `Belief.pmf_sum_one`, `Lipschitz.l1_lipschitz` and `Lipschitz.firstMoment_lipschitz` are
  **unconditional in `θ`** — they never divide, so no side condition is needed (trap P-2).
* **Weights.** `γ_i ≥ 0`, `Σ γ_i = 1` are carried as explicit hypotheses
  (`perRoundPenaltyDiff_le`), never assumed globally. `TSDPP.weight_le_one` extracts `γ_a ≤ 1`.
* **Endpoint vs interior.** Lemma 2's bound is proved on the **closed** interval `[0,1]`, not the
  open one: `arm_deriv_abs_le_one` handles `u = 0` (i.e. `θ = 1`) by direct computation because
  the Bernoulli corollaries of `TSDPP/Ineq.lean` need `u > 0`. See trap P-3.
* **`C` and `D`.** `δ ≤ C` and `λ + δ ≤ L` are *hypotheses* of `perRoundPenaltyDiff_le`, not
  derived facts — the paper has no proof of either (GAP-3).

## 5. Rejected routes (with the reason each was rejected)

* **J-1. Formalize `BR(T) = O(√(L³T log T))` end-to-end.**
  *Route*: set up the full episodic MDP, define `J^θ_{π,t}`, `BR(T)`, and prove Eq (19) as a `IsBigO` statement.
  *Rejected because*: it requires (i) a trajectory measure space for the coupled process
  `(θ*, θ^l, A_t, X_t)`, (ii) conditional-expectation algebra over that space, (iii) Bellman operators and
  their telescoping (R10), (iv) Beta concentration (R11). Items (iii) and (iv) are each independently
  substantial; Mathlib has no MDP/Bellman library and no Beta-concentration result. Attempting it would
  have produced `sorry`s, which the constraints forbid. Replaced by the honest decomposition in §3 plus GAP-1/2.
* **J-2. `native_decide` / `decide` on the finite cases.** Rejected: explicitly forbidden.
  Would also be unsound for the `ℝ`-valued statements, which are the actual content.
* **J-3. State Lemma 5 (Beta concentration) as an axiom or a `variable`.** Rejected: `CLAUDE.md` forbids
  introducing axioms to close a goal. It is recorded as GAP-2 instead.
* **J-10. Four attempts to reach the paper's constant `1/8` in Lemma 5** (full statements in GAP-2c;
  the union-bound ceiling is `0.123302`, twelve thousandths short).
  * **(a) 2-D Chernoff on `X − Y`.** Correct order (`≈ e^{−α/4}` at `ρ=1`), but needs
    `E[e^{λX}] = ₁F₁(α; α+β; λ)`. Mathlib has no confluent hypergeometric function and no route
    to one that is shorter than building it. *This is the obstruction that costs the constant.*
  * **(b) Exact conditioning `∫_0^{1−μ} φ(y+μ) f_Y(y) dy`.** Effective constant `≥ 0.2367` —
    comfortably past `1/8` — but the resulting integral needs a uniform-in-`(α,β)` lower bound on
    `B(α,β)`, i.e. Laplace/Stirling asymptotics. More work than (★) for a constant GAP-2b shows is
    asymptotically irrelevant.
  * **(c) Improve the one-sample bound `φ`.** Impossible: minimising the two-sided family
    `(1−λ(1−t))^{−α}(1+λt)^{−β}` over `λ` returns `φ` *exactly* (the Γ-factors cancel). Verified
    numerically at `ρ = 1, t = 1/2`, where the "improved-looking" form `t^{1+ρ}((1+ρ)/(cρ))^ρ`
    collapses to `φ`; an earlier session note claiming `φ` is beatable by a factor `(1+ρ)^{−α}` was
    an algebra slip, not a real gain.
  * **(d) Chebyshev / variance / integer-moment Markov.** Give polynomial decay only; the paper
    needs an exponential tail. Rejected on the form of the conclusion, before any formalization.
* **J-4. Define the AoI chain as `Kernel`-valued and use Mathlib's `ProbabilityTheory.Kernel` API.**
  Rejected: for R5/R9/R12a the closed-form finite-support law `beliefPMF` is both simpler and *stronger*
  (it gives exact equality rather than an a.e. statement), and it keeps the development free of
  measure-theoretic obligations that would not be discharged. The `Kernel` route is retained only for
  R1 where the chain itself is the object of study.
* **J-5. Avoid calculus by using the algebraic inequality `|a(1−a)^x − b(1−b)^x| ≤ |a−b|`.**
  Rejected: no algebraic path found that is shorter than MVT (`Convex.norm_image_sub_le_of_norm_deriv_le`);
  the MVT route needs only `sup|f'| ≤ 1` on `[0,1]`, which is a clean polynomial estimate. See trap P-3.
* **J-7. Prove Eq (25)'s `sup|f'| ≤ 1` by clearing denominators.**  *Route*: substitute
  `c = (1−u)/u` and prove `1 − (k+1)c ≤ (1+c)^{k+1}` from Bernoulli, then multiply back by
  `u^{k+1}`.  *Rejected because it is false*: Bernoulli gives `(1+c)^{k+1} ≥ 1 + (k+1)c` only for
  `c ≥ −2`, and for `c < 0` (i.e. `u > 1/2`) the inequality `1 − (k+1)c ≤ (1+c)^{k+1}` reverses.
  This route works for the *positive* half (Eq (25)'s first term, `Ineq.pow_add_weighted_le_one`)
  and silently fails for the negative half `(k+1)u^k − (k+2)u^{k+1} ≤ 1`.  Replacement:
  rewrite the expression as `u^{k+1} − (k+1)u^k(1−u)` and drop the non-negative subtracted term
  (`Ineq.succ_mul_pow_sub_le_one`).  See trap P-9.
* **J-8. Let `ring` shift the exponent index in Lemma 2's general-`x` statement.**  *Route*:
  prove `u^{k+1} + (k+1)u^k(1−u) ≤ 1` and derive the general-`x` form by `ring`.  *Rejected
  because* `ring` treats `u^x` and `u^{x−1}` as independent atoms and cannot relate them; the
  index shift must be done by `pow_succ'` + `Nat.add_sub_cancel` inside an explicit case split.
  See trap P-8.
* **J-9. Bound Eq (36) by Lemma 6's `λ + δ ≤ C + D`.**  *Route*: use the copy-AoI bound from
  Lemma 6 to turn `δ(λ+δ)` into `C(C+D)`.  *Rejected*: it gives `C(C+D)` where the paper prints
  `LC`, and then Eq (38)'s coefficient `½C² + (2C²+2CD+C)L` does not come out — the expansion
  leaves an unmatched `2C²L` term.  The `LC` printed in Eq (36) is valid for a different reason:
  inside an episode of length `L` the copy-AoI satisfies `λ + δ ≤ L` trivially, giving
  `δ(λ+δ) ≤ C·L`.  Both routes are true; only `LC` reproduces the paper's constant.  Verbatim
  check of the expansion is in §8.  See trap P-13.
* **J-6. Formalize the belief state as `E[X | H]` via `MeasureTheory.condExp`.** Rejected: the paper's
  record `(λ_i, δ_i)` is a *sufficient statistic*, and proving sufficiency would be a detour. We instead
  prove the law (R5) and take its mean (R6); the fact that the record determines the law is exactly the
  content of Lemma 2's preamble.

* **J-11. Close the paper's *actual* Lemma 5 range, `0 ≤ r ≤ 1` (the natural repair after P-64).**
  *Route*: restate the target on the range the paper printed, with the paper's constant `1/8`, and
  find any route that closes it.  *Rejected because all three available routes are dead*, and they
  die for three different reasons — this is worth recording precisely, because "restate it on the
  right range" sounds like a paperwork fix and is not one.
  * **(a) Reuse this file's union split.** Impossible by P-64: the split needs `t₁ − t₂ = μ(1+δ₁−δ) ≤ rμ`,
  i.e. `r ≥ 1`, and at `r ≤ 1` the small-lower-tail choice `δ → 0` forces `δ₁ ≤ r−1 ≤ 0`, outside the
  admissible range `δ₁ > 0`. The method's range and the statement's range have disjoint interiors.
  * **(b) One-sample Chernoff on `Pr(X ≥ rμ)`.** The Gamma–Markov bound is
  `(1−w)^{−α}(1 + w·t/(1−t))^{−β}` with `t = rμ = rα/(α+β)`; for `r ≤ 1` the threshold is **at or below
  the mean**, where the optimiser degenerates and the bound returns `1` — no information. This is not
  a technicality: the true probability at `r = 1` is **`0.495857`** at `α = 1000`, `β = 100α` —
  essentially one half, against a target `e^{−α/8}` that is exponentially small. The one-sample route
  is not merely weak here; the quantity it estimates is not small.
  **[CORRECTED 2026-09-18 — traps P-69.]** This read "for large `α` the true probability is `≥ 1/2`".
  It is **strictly below `1/2` at `r = 1`** for every `α` (`0.369711`, `0.458552`, `0.486899`,
  `0.490737`, `0.495857` at `α = 1, 10, 100, 200, 1000`), rising monotonically to `1/2` from below —
  the Beta is right-skewed, so its median is below its mean. The bound is avoided, not attained. The
  conclusion is unaffected and in fact slightly stronger this way (the value is large, not
  marginal), but the inequality as written was false. At `r = 1/2` the claim *is* true for all
  `α ≥ 1` (`0.608792` at `α = 1`, `≈ 1` above), so the corrected statement is: **the one-sample
  probability is `≈ 1/2` at the mean, and no constant-exponent Chernoff bound can separate it from
  `e^{−αr²/8}`.**
  * **(c) The exact two-sample union bound.** The split of §4 is valid for **any** `s` (its hypothesis
  is `t₁ − t₂ ≤ s`, nothing about `r`); only the *instantiation* `t₁ = μ(1+δ₁)` needs `r ≥ 1`.
  Evaluating the resulting expression with **exact** Beta tails instead of Chernoff factors *passes*
  at every cell tested — but by much less than first recorded, and the Markov/Chernoff surrogate of
  the same split fails at the majority of cells. So the obstruction is entirely the tail *estimate*,
  not the split.
  **[CORRECTED 2026-09-18 — traps P-69.]** The figures here were "worst `bound/target` ratio
  `0.0052`, i.e. ~190× slack" and "fails at 42 of 48 cells". Neither is reproducible from any grid
  the two independent routines could reconstruct.  Measured: the worst ratio on `0 ≤ r ≤ 1` is
  **`0.4530`** (at `α = 1, ρ = 1000, r = 0.1`; the sup over the region is `0.5`, approached as
  `r → 0`), so the exact route carries only **~2.2× slack at its worst point**, not 190×; and on a
  120-cell grid the surrogate exceeds the target at **80 cells**, worst excess **`2.59×`**
  (`α = 200, ρ = 1000, r = 1`). The qualitative conclusion survives — the exact route holds
  everywhere tested and the surrogate does not — but "comfortably viable" was an artefact of two
  unreproducible numbers, and the exact route is *tighter* than claimed. See P-69.
  An exact Beta tail at non-integer `(α,β)` is an
  incomplete beta / `₁F₁`, which GAP-2c excludes; and the integer-parameter case, where the tail *is*
  an explicit finite binomial sum (`1 − I_s(α,β) = Σ_{j<α} C(n,j) s^j (1−s)^{n−j}`, `n = α+β−1`),
  still needs that polynomial bounded **uniformly in `(α,β)`** by `e^{−cαr²}` — a large-`n` asymptotic
  estimate of a degree-`n` polynomial, not a rewrite. Not attempted; no shorter route found.

  **And closing it would not rescue the paper.** Even a complete proof of Lemma 5 on `0 ≤ r ≤ 1`
  leaves Eq (33) unjustified, because Eq (33) applies the lemma at
  `r = max{1, √(8 log T/α)} ≥ 1` — outside the range just proved. So the repair restores the *lemma*
  and not the *theorem that cites it*. This is the single most important thing to know before
  investing in (c): **there is no range on which both the paper's application and the paper's bound
  are simultaneously valid**, and the P-64 table is the witness.

* **J-12. ACCEPTED ROUTE — refute the registered target inside Lean, and let the refutation be the
  deliverable.** `CLAUDE.md` item 1 reads "给出 `<ROOT_STATEMENT>` 的完整证明**或反证**", so a
  machine-checked counterexample discharges the same obligation a proof would. Chosen 2026-09-18,
  after J-11 established that no repair of the *positive* statement is reachable from this
  toolkit.

  The obstruction is that a refutation needs a **lower** bound on a probability, and every tool in
  `TSDPP/` produces *upper* bounds (Markov, Chernoff, union, Cantelli, Chebyshev). The route that
  works replaces tail estimation by an **elementary containment**:

  ```
      {X ≥ t} × {Y ≤ u}  ⊆  {|X − Y| ≥ s}      whenever  s ≤ t − u ,
  ```

  which holds because `X − Y ≥ t − u ≥ s > 0 ⟹ |X − Y| = X − Y ≥ s`. It needs no measure theory
  beyond `Measure.prod_prod`, no Chernoff, and no optimisation: it costs one product of one-sample
  tail probabilities. `Scratch/MainBox.lean` proves the containment and the assembly (CLOSED).

  **Witness selection is the whole design problem**, and it is a Lean-cost problem, not a
  probability problem:

  | route | viable? | why not |
  |---|---|---|
  | numerically strongest witness `(5,500,10)` (`1.4e5×` violation) | no | certificate needs `(1−t)^500`; elementary but a 500-term binomial |
  | the exact two-sample value `∫_s^1 f(x)F(x−s)dx` | no | that **is** the answer, so it needs the two-sample integral — strictly harder than the one-sample tails the containment already buys (J-11(c) is the same wall) |
  | `α ≥ 2` | no | `betaPDFReal` carries a positive power of `x`, so the density integral stops being a single power |
  | `α = 1`, `β = 100`, `r = 10` | no | the target **holds** there (`c_eff = 0.111730 > 0.11`) — this is the near miss that makes the choice non-obvious |
  | **`α = 1`, `β = 100`, `r = 14`** | **yes** | `α = 1 ⟹ beta 1 B = 1/B` and `x^{1−1} = 1`, so the density is exactly `B(1−x)^{B−1}` and the tail is the **single power** `(1−t)^B`; the one real-analysis node becomes `∫_a^b B(1−x)^{B−1} dx`, a polynomial integral |

  The constant `c₀ = 11/100` is irrelevant to the refutation's existence (the witness violates the
  paper's `1/8` too, by `353×` at the true value), which is why the refutation does not need the
  retracted `c₀` derivation of P-62.

  **Cost paid for choosing a Lean-cheap witness**: the provable lower bound `LB` is `4.664×` below
  the true probability, so the machine-checked statement certifies `75.79×` where the truth is
  `353.48×`. That is the correct trade — the refutation needs `> 1×`, and everything above it is
  margin. Full certificate: `cards/L5-REFUTATION.md`.

## 6. Traps (Lean-specific), logged as encountered

* **P-1 (paper's own index slack).** Eq (4) vs Eq (9)/(35) off-by-one. Resolved by pinning Eq (9)'s
  convention; documented in §4. *Not* a Lean trap, but it is a trap for the formalizer — it silently
  changes which `δ` the bound in R13 applies to.
* **P-2.** `∑ x ∈ range n, x * (1-θ)^x` has no direct Mathlib lemma. Route: rewrite with
  `geom_sum_eq` on the *derivative* identity, or prove the closed form by induction using
  `Finset.sum_range_succ` and `ring`. Chosen: induction + `ring`, since it avoids division-ring
  side conditions on `1-θ ≠ 1`. (Substituting `geom_sum_eq` gives `(∑ x q^x)(q-1)... ` and forces a
  `q ≠ 1` case split that induction does not.)
* **P-3.** `Convex.norm_image_sub_le_of_norm_deriv_le` is stated for `RCLike 𝕜` and `NormedAddCommGroup G`;
  instantiating at `𝕜 = ℝ`, `G = ℝ` makes `‖·‖ = |·|`, which is fine, but the derivative hypothesis is
  `‖deriv f x‖ ≤ C` over the closed interval — so the bound must be *uniform on* `[0,1]`, including
  endpoints. Verified numerically first (`scripts/numeric_check.py`) that `sup|f'| = 1` exactly, attained
  at `θ=0`; a naive `interval_cases`-free estimate that assumed the sup was in the interior would fail.
  This numeric check is why the card was written with `θ ∈ [0,1]` closed rather than open.
* **P-4.** The numeric falsifier showed Lemma 2's constant `2δ` is **tight** (ratio `1.0000000000000113`
  after 30 000 random trials, i.e. `= 1` up to floating error). Consequence: the proof may not "improve"
  `2δ` to `δ` anywhere; an early proof sketch did, and the falsifier caught it. Logged because the paper's
  own Eq (25) argument is what forces `2δ` (δ terms of size `|Δθ|` plus one term of size `δ|Δθ|`).
* **P-5.** Summing `if x < δ then … else if x = λ+δ then … else 0` over `range (λ+δ+1)` requires a
  disjointness side condition (`δ ≤ λ+δ`, immediate). Using `Finset.sum_ite` naively produces goals about
  `x < δ ∧ x = λ+δ` which are refuted by `omega`.
* **P-6.** `Real.rpow` vs `^` (monoid power): `betaPDFReal` uses `x ^ (α - 1)` with `α : ℝ`, i.e. `rpow`.
  When the parameters are *natural* (`α + A` with `A : ℕ`) the statements must move between `rpow` and
  `Nat`-power. Route: keep parameters as `ℝ` throughout and use `Real.rpow_add`, `Real.rpow_natCast`,
  `Real.rpow_one`; do **not** restate in `ℕ`-powers, which would break `betaPDFReal`'s form.
* **P-7.** `betaMeasure` is defined by `volume.withDensity (betaPDF α β)` with `betaPDF : ℝ → ℝ≥0∞`.
  A measure-level conjugacy statement must be stated as `withDensity` of an `ℝ≥0∞` function; the natural
  `ℝ`-valued likelihood has to be pushed through `ENNReal.ofReal`, and `ofReal` does not commute with
  multiplication without nonnegativity. Route: prove the `ℝ`-valued density identity first (that is the
  actual mathematical content), then derive the measure statement with explicit nonnegativity.

* **P-8 (`ring` cannot see through a shifted `ℕ` exponent).** In `Ineq.pow_add_weighted_le_one'`
  the general-index statement `u^x + x·u^{x−1}(1−u) ≤ 1` cannot be derived from the `k+1` form by
  `ring`: `u^x` and `u^{x−1}` are *distinct atoms* to `ring`'s normaliser, so it has no way to
  relate them.  Also `u^{0−1}` is `u^0 = 1` under truncated `ℕ`-subtraction, so the two forms have
  genuinely different degenerate cases.  **Fix**: `rcases x with _ | k`, then
  `simpa [Nat.cast_add, Nat.add_sub_cancel]`.  Same shape recurs in
  `Ineq.succ_mul_pow_sub_le_one'`, where a `have hgoal : ((k:ℝ)+1+1) = (k:ℝ)+2 := by ring` must be
  supplied as a simp lemma or the cast of `k+1+1` will not match `k+2`.
* **P-9 (clearing denominators is not sign-safe).** Provenance: `Ineq.succ_mul_pow_sub_le_one`.
  The substitution `c = (1−u)/u` turns `u^{k+1} + (k+1)u^k(1−u) ≤ 1` into a Bernoulli instance and
  works.  Applying the *same* substitution to `(k+2)u^{k+1} − (k+1)u^k ≤ 1` gives
  `1 − (k+1)c ≤ (1+c)^{k+1}`, which Bernoulli does **not** prove and which is **false** for
  `c < 0`.  **Fix**: don't clear denominators; rewrite as `u^{k+1} − (k+1)u^k(1−u)` and bound by
  `u^{k+1} ≤ 1`.  Logged because the two half-inequalities look symmetric and are not.
* **P-10 (the paper's printed derivative is wrong at `x = 0`).**  Eq (25) prints
  `f'(ξ) = (1−ξ)^{x−1}(1−(x+1)ξ)`.  Under Lean's truncated `ℕ`-subtraction `(1−ξ)^{0−1}` is
  `(1−ξ)^0 = 1`, not `(1−ξ)^{−1}`, so the printed form evaluates to `1−ξ` at `x = 0` while the true
  derivative of `θ(1−θ)^0 = θ` is `1`.  **Fix**: state the derivative un-truncated as
  `(1−θ)^x − θ·x·(1−θ)^{x−1}`, which is correct at every `x`; `Lipschitz.armTerm_deriv_eq` proves
  it equals the `(x+1)(1−θ)^x − x(1−θ)^{x−1}` normal form used by the bound.  This is a *paper*
  defect surfaced by the formalization, not a Lean defect.
* **P-11 (`∑` swallows a following `=`).**  Symptom: `typeclass instance problem is stuck
  IsOrderedRing ?m`, with a metavariable, on a line that looks like ordinary arithmetic.
  Cause: `∑ x ∈ s, f x = g` parses as `∑ x ∈ s, (f x = g)` — the body of `∑ … , …` extends as far
  right as possible, so an unparenthesised `=` after the body is absorbed and Lean then tries to
  find a semiring structure on `Prop`.  **Fix**: ascribe the type of the sum
  (`(∑ x ∈ s, f x : ℝ)`) or wrap the whole sum in parentheses.  Hit in
  `Regret.stateTerm_le`.
* **P-12 (`Nat.cast_nonneg` has an undetermined codomain).**  Symptom: the same "stuck
  `IsOrderedRing`" message, but at a *hypothesis* rather than an expression.  Cause:
  `Nat.cast_nonneg n` elaborates to `(0 : ?α) ≤ (n : ?α)` and inside a `nlinarith [ … ]` list
  nothing pins `?α`, so instance search stalls before `nlinarith` ever runs.  **Fix**: bind it
  first with an explicit type (`have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := Nat.cast_nonneg δ`) and pass the
  local hypothesis.  General lesson: **never pass an unapplied polymorphic lemma directly to
  `linarith`/`nlinarith`; pin its type with a `have` first.**
* **P-13 (`nlinarith` will not invent the right product).**  `stateTerm_le`'s final step needs
  `(2δ|θ−θ'|)·((C+D)L) ≤ 2C(C+D)L|θ−θ'|` from `δ ≤ C`.  `nlinarith` fails: it must multiply the
  hypothesis by `2|θ−θ'|(C+D)L`, and it has no reason to pick that factor.  **Fix**: decompose
  into an explicit `calc` that factors `δ` out first
  (`… = (2|θ−θ'|((C+D)L))·δ ≤ (2|θ−θ'|((C+D)L))·C = …` via `ring`, `mul_le_mul_of_nonneg_left`,
  `ring`).  General lesson: `nlinarith` closes *linear* consequences and simple products; a step
  that requires choosing a multiplier should be written as an explicit `calc`.
* **P-14 (unused-hypothesis linter as a proof defect detector).**  `Regret.episodeRegret_le` and
  `Regret.regret_le` were first stated with `hK : 0 ≤ K` and `hdelta : ∀ t, 0 ≤ delta t`; the
  linter reported both unused.  Investigation showed the triangle-inequality route
  (`abs_sum_le_sum_abs` then `sum_le_sum`) genuinely never uses either, so the hypotheses were
  dropped, yielding strictly stronger statements.  Logged because "silence the linter" would have
  hidden a real sharpening.  (They are still needed *downstream*, where `K` is multiplied — that
  is recorded as `regretCoeff_nonneg`.)
* **P-15 (`lake build` does not build what `TSDPP.lean` does not import).**  Symptom: `lake build`
  reports "Build completed successfully (8933 jobs)" while `lake env lean TSDPP/Assembly.lean`
  later fails with "object file `TSDPP/Assembly.olean` does not exist".  Cause: the lakefile sets
  `defaultTargets = ["TSDPP"]`, which builds the *root module* `TSDPP.lean`, not every `.lean` file
  in the library directory.  A file that nothing imports is never compiled by `lake build`.
  **Fix**: keep `TSDPP.lean` importing every module (it now does), and treat "does the root import
  it?" as part of the definition of CLOSED in §3.  Also: `lake env lean <file>` does **not** build
  that file's dependencies — run `lake build TSDPP.<Dep>` first.
* **P-16 (`simpa` and ℝ instance diamonds).**  Symptom: `simpa` fails on goals that are
  definitionally equal, complaining about `Real.instAddCommGroup` vs
  `Real.normedCommRing.toCommRing.toAddCommGroup`, or about `(fun x => 1) - id` vs `fun t => 1 - t`.
  **Fix**: replace `simpa`/`convert … ` with `convert … using 1` plus one explicit subgoal per
  remaining obligation (`· funext t; rfl`, `· ring`).  Hit repeatedly in
  `Lipschitz.hasDerivAt_armTerm`.
* **P-17 (`field_simp` already closes the goal).**  Symptom: `No goals to be solved` at a `ring`
  placed *after* `field_simp`.  Cause: in this Lean version `field_simp` finishes by normalising
  with an internal ring step.  **Fix**: drop the trailing `ring`.  Hit in `Ineq.lean` and again in
  `Conjugacy.lean` (independently, by a different workstream) — logged twice because the second
  occurrence confirms it is systematic rather than incidental.
* **P-18 (`∑ _t ∈ range L, f l t` binds `_t`, leaving `t` free).**  Symptom: a sum that "should"
  vary in its index does not — `sum_le_sum` reports the expected type as
  `∀ i ∈ range L, delta l t ≤ …` with `t` *not* varying, and the error compares `t` against `t✝`.
  Cause: writing the binder as `_t` (a habit picked up from `Tail.lean`, where the summand is
  index-independent and the name genuinely does not matter) leaves every `t` in the *summand*
  free, so Lean auto-binds it as an outer variable.  **Fix**: name the binder after the variable
  the summand actually uses (`∑ t ∈ range L, delta l t`).  **Process failure, logged as such:**
  this was written into `Theorem2.lean` while porting the `_t` style from `Tail.lean` without
  checking that the summand there was constant.  A one-line statement re-read would have caught
  it; the lesson is that notation copied across modules must be re-derived, not pattern-matched.
* **P-19 (a "tight constant" claim must be exhibited, not asserted).**  `Rate.rate_core` proves
  `2L√(8Z) + B ≤ 7√(L⁴Z)` when the radius constant is the paper's `8`.  The `7` was derived as
  `6 + 1`, and the natural suspicion is that the derivation is loose.  Numeric maximisation gives
  `max (2L√(8Z)+B)/√(L⁴Z) = 6.656854 = 2√8 + 1`, attained at `L = m = logT = η = 1`, `B = √log T` —
  so any constant below `6.657` fails on that explicit witness, and `7` is within `5%` of optimal.
  Logged as the mirror image of P-4: there, tightness forbade *loosening* an inherited constant;
  here, tightness forbids *assuming* a derived one is slack.  Both are decided numerically before
  the Lean proof is trusted.
  **Update (task #12) — the same trap, re-armed, and this time it fires in reverse.**  The
  artifact's radius constant is now `K₀ = 100/11`, not the paper's `8`, so the declaration proves
  `2L√(K₀Z) + B ≤ 8√(L⁴Z)`.  The witness above is unchanged (`L = m = logT = η = 1`, `B = √log T`)
  but its value moves from `2√8 + 1 = 6.656854` to `2√(100/11) + 1 = 7.030226`.  Two consequences
  that this entry exists to warn about:
  * the *previously* tight-and-valid constant `7` is now **refuted** by that same explicit witness
    (`7 < 7.0303`), so the substitution `7 → 8` is forced, not cosmetic;
  * the first summand alone is `2√(100/11) = 6.030227`, still `< 7`, so *the intermediate bound
    `2L√(K₀Z) ≤ 7√(L⁴Z)` survives and only the `+1` crosses*.  A reader who checks only the first
    summand (as one naturally does, since that is where the substitution bites) will conclude `7`
    is fine and be wrong by `0.0303`.  Both numbers must be checked; see P-48 for the version of
    this mistake that a compiler *can* catch.
* **P-20 (do not run a mutate-restore cycle in a command that a timeout can kill).**  A negative
  control for `check_axioms.sh` truncated `TSDPP/Assembly.lean`, ran the gate, and restored the
  file from a backup — all in one shell invocation.  The invocation exceeded the tool timeout and
  was killed **between the mutation and the restore**, leaving a real source file truncated on
  disk.  It was caught and restored, but the failure mode is general: any harness that temporarily
  breaks the tree must either (a) do the mutation in a scratch copy outside the repo, or (b) be
  split into separate steps so no single killable command spans the mutation.  Recorded because
  the near-miss was silent — the build would still have "succeeded" on a stale olean.
* **P-21 (a checker that counts verdicts fails on declarations with *no* axioms).**  Adding
  `copyStep`, `copyStep_self`, `copyStep_other` to `Audit.lean` broke the gate with
  `FAIL: 43 declarations audited but 40 verdicts reported`.  Nothing was wrong: `#print axioms`
  prints **nothing at all** when the axiom set is empty, and those three are a `def` and two `rfl`
  lemmas, so Lean emitted no line for them.  An empty axiom set is the *strongest* possible
  outcome, and the old `declared == reported` count rejected it.  Fixed by making the check
  name-level: every verdict must name something declared, and anything declared with no verdict is
  reported as "empty axiom set" rather than as a missing verdict.  This is the second time this
  gate failed in the direction of false rejection (see `copyStep_iterate` and the
  string-equality-to-set-membership fix above); the general lesson is that a verification gate must
  be written to *accept* strictly stronger evidence, or it will be "fixed" later by someone who
  reads the failure as noise and weakens the check.  Negative-controlled by feeding the check
  synthetic input (a phantom name must fail, real names must pass) rather than by mutating
  `Audit.lean` — see P-20 for why that distinction is not pedantic.
* **P-22 (a parametrised identity checked at a fixed point proves nothing).**  Two transcriptions
  `ρs(1/ρ+1−s)^ρ` and `ρs(1+(1−s)/ρ)^ρ` of the same *derived* quantity agree **iff `ρ = 1`** —
  and `ρ = 1` is exactly where the spot-check was made.  The wrong one was used for a whole
  numerics run and produced a false ceiling.  Rule: when two candidate forms can disagree, test on
  a value where they provably differ, and test at more than one.  See §8.
* **P-23 (a supremum over a limit is invisible to a grid).**  `sup_ρ m(ρ)` for the Lemma 5 union
  bound is *attained at `ρ→∞`*, not at any finite `ρ`.  A dense grid in `ρ` up to `10³` reports
  "holds"; the truth is "fails", and only the closed-form crude bound — in which `ρ` cancels — shows
  it.  General rule for this project: **any `sup` over a shape parameter must be reduced to a form
  where that parameter has dropped out before a grid is trusted.**  The trap is the mirror image of
  the grid-resolution failures already logged (truncating `(1−s)^ρ`); here the grid is dense enough,
  it is the *domain* that is wrong.

  *Recurrence, 2026-09-17 (three more instances, both directions).*  P-23 fired again during the
  P-62/P-63 sweep, and not only against `sup`:
  **(1)** `m(ρ) = min_δ max(A,B)` was tabulated on a uniform `δ`-grid, reporting `m(0.1) = 0.420160`
  and a downturn at small `ρ`; the true value is `min_δ max = 0.125893`.  The optimum sits at
  `δ → ρ⁻` where `(1−δ/ρ)^ρ` collapses at scale `e^{−1/ρ}`, which a uniform grid cannot reach.  The
  false reading was then used to *withdraw a correct monotonicity claim* — a grid artifact can do
  damage in the retracting direction too.
  **(2)** The same sweep's `r*(s₀)` and residual-`v` tables were floored by the grid's smallest
  `δ = 1e−15`, since `B(δ) ≳ δ·e → 0` as `δ → 0`; the reported infimum was `2.7e−15` where the truth
  is `≈ 3.8e−32`.  A grid bracket is a **false lower bound on an infimum**, exactly as it is a false
  upper bound on a supremum.
  **(3)** A `sup_ρ` measured on `ρ ∈ {0.5, …, 10⁸}` was generalised to `ρ ∈ (0,∞)`; both turning
  points live at the small-`ρ` end the grid never sampled.
  **(4)** *A new shape, caught in the act.*  Re-checking instance (1) with a corrected
  boundary-layer parametrisation `δ = ρ(1−e^{−t})`, the optimizer was allowed to range over
  `δ ∈ (0, ρ)` — silently **dropping the hypothesis `hδ1 : δ < 1`**, which for `ρ > 1` is the
  binding constraint.  It then reported `m(2) = 0.5`, `m(5) = 0.0016`, `m(10) = 1e−9` (the
  `δ → ρ⁻` limit of `B`, i.e. `ρ^{1−ρ}`) against the true `0.819146`, `0.858605`, `0.871392` — two
  to nine orders of magnitude wrong, and *smaller*, so it would have "corrected" a correct table.
  Fixing the domain to `(0, min(1,ρ))` reproduces the recorded table to six digits
  (`0.603259, 0.750000, 0.819146, 0.858605, 0.871392`, and `m(0.1) = 0.125892541`).  **A grid
  failure need not be about resolution or domain *extent*; it can be a dropped hypothesis.**  Revert
  to the statement and re-read every side condition before trusting a re-optimisation.
  **Strengthened general rule:** a grid bracket is *bracketing in neither direction* — it can hide a
  `sup` at a limit and manufacture a floor under an `inf`.  Before either is trusted, reduce the
  quantity to a form in which the shape parameter has dropped out, or probe the boundary layer
  explicitly and in log-scale — here `δ → 0` (use `δ = e^{−t}`) and `δ → ρ⁻` (use
  `δ = ρ(1−e^{−t})`, the scale on which `(1−δ/ρ)^ρ = e^{−ρt}` becomes geometric).
* **P-24 (no real-exponent Bernoulli inequality in Mathlib).**  For the GAP-2d obligations one needs
  `(1 − t/n)^n ≤ e^{−t}` and `(1 + t/n)^n ≤ e^{t}` with a **real** `n = ρ`.  Mathlib only has the
  *natural*-`n` versions: `Real.one_sub_div_pow_le_exp_neg {n : ℕ} {t : ℝ} (ht' : t ≤ n) :
  (1 - t/n)^n ≤ exp(-t)` (`Mathlib/Analysis/Complex/Exponential.lean:643`) and
  `Real.one_add_inv_pow_le_exp {n : ℕ}`.  `grep -rn "one_add_div_pow_le_exp\|div_pow_le_exp"`
  over `Mathlib/` returns nothing, so both real-`n` forms must be re-derived.  Route used
  (`Scratch/UnionBound.lean`, `rpow_one_sub_div_le_exp_neg` / `rpow_one_add_div_le_exp`): split on
  `0 ≤ 1 − t/n`; in the `> 0` branch `Real.log_le_sub_one_of_pos` gives `log(1 − t/n) ≤ −t/n`,
  multiply by `n > 0` via `mul_le_mul_of_nonneg_right`, then `rw [Real.rpow_def_of_pos h]` and
  `Real.exp_le_exp.2`; the `= 0` branch is `Real.zero_rpow (ne_of_gt hn)`.
  **Asymmetry to remember:** the `−` form needs `t ≤ n` but *not* `t ≥ 0`; the `+` form needs
  `0 ≤ t` as a hypothesis, because otherwise `1 + t/n < 0` and `Real.rpow_def_of_pos` has no
  `0 <` fact to consume.  Statement it as an explicit hypothesis or the lemma is not true.
* **P-25 (`eq_or_lt` on `0 ≤ x` yields `0 = x`).**  `rcases hb.eq_or_lt with h | h` for
  `hb : 0 ≤ x` gives `h : 0 = x`, so the rewrite is `rw [← h]`.  Writing `rw [h]` fails with
  "Did not find an occurrence of the pattern `0`" — a misleading message, since the goal visibly
  contains a `0`; the pattern being searched for is the whole LHS `x`.
* **P-26 (`field_simp` closing the goal makes a trailing `ring` a hard error).**  `by field_simp; ring`
  is *not* safe: when `field_simp` already closes the goal (it does for
  `ρ * (29/(50ρ)) = 29/50`), the `;`-sequenced `ring` runs on zero goals and Lean 4 hard-errors with
  "No goals to be solved" — an error, not a warning.  Use `by field_simp; try ring` (`try` absorbs
  the no-goals failure).  Also `field_simp` needs the `≠ 0` fact for each denominator to be findable
  in context; with `hρ : 0 < ρ` in scope it is not always picked up, so bind
  `have hρne : ρ ≠ 0 := ne_of_gt hρ` first.
* **P-27 (`rw` does not close up to defeq; `Real.exp_neg` rewrites every occurrence).**  After
  `rw [Real.exp_neg]` a goal of the shape `a * (exp x)⁻¹ = a / exp x` is *definitionally* closed but
  `rw` leaves it open — and the obvious repair `rw [div_eq_mul_inv]` fails to fire, because the `/`
  in the target is already the same `mul`/`inv` node, so there is no `/` pattern left to match.
  Fix: `rw [Real.exp_neg]; rfl`.  Separately, `rw [Real.exp_neg]` rewrites **all** occurrences of
  `exp (-·)`, so it must not be used on a goal that mentions `exp (-·)` on both sides — isolate one
  side in a `calc` step, or go through an auxiliary `have`.
* **P-28 (which exp bound points which way).**  `Real.sum_le_exp_of_nonneg {x} (0 ≤ x) (n) :
  ∑_{i<n} x^i/i! ≤ exp x` is a **lower** bound and is only valid for `x ≥ 0`; a partial sum can never
  produce an upper bound on `exp`, and a partial sum at a negative argument proves nothing without
  an alternating-series argument.  `Real.exp_bound {x} (|x| ≤ 1) {n} (0 < n)` returns an `|·|` bound
  that must be pushed through `abs_sub_le_iff` before use.  The directly usable upper bound is
  `Real.exp_bound' (h1 : 0 ≤ x) (h2 : x ≤ 1) {n} (0 < n) : exp x ≤ (∑_{m<n} x^m/m!) + x^n (n+1)/(n! n)`
  — that is what closes `e^{53/100} ≤ 50/29` at `n = 4`
  (`1.695258 + (0.53)^4·5/96 = 1.699372 ≤ 1.724138`).
  Mechanical note: `norm_num [Finset.sum_range_succ] at h` is what actually evaluates the range sums;
  plain `norm_num at h` does not reliably unfold `∑ i ∈ Finset.range k, x^i/i!` for literal `k`.
* **P-29 (GAP-2d's case-2 obligation has a cheaper certificate than the one prescribed).**  GAP-2d
  asks for `ρ^{1−ρ} ≤ (29/50)^{21/50}` via *strict monotonicity* of `ρ ↦ (1−ρ) log ρ` on `(0,1)`.
  That monotonicity needs `1/ρ − 1 − log ρ > 0`, i.e. `log ρ < 1/ρ − 1`, which is derivable
  (`Real.log_lt_sub_one_of_pos` gives `log ρ < ρ − 1`, and `ρ < 1/ρ` for `ρ < 1`) — but it is not
  needed.  Substituting the *same* inequality `Real.log_le_sub_one_of_pos` once gives
  `(1−ρ) log ρ ≤ −(1−ρ)²`, and `1 − ρ ≥ 21/50` gives `≤ −(21/50)²`, so
  `ρ^{1−ρ} = exp((1−ρ) log ρ) ≤ exp(−(21/50)²) = 0.838284 ≤ e^{−11/100} = 0.895834`.
  This is *weaker* than the prescribed `(29/50)^{21/50} = 0.795499` (both clear the `e^{−c₀}` bar
  with ≥ 6% to spare) but strictly shorter: no monotonicity, no derivative, no `Real.rpow_le_rpow`,
  no `log_rpow`.  Discharged by `Real.rpow_def_of_pos` + `Real.exp_le_exp.2` +
  `nlinarith [sq_nonneg ((1 − ρ) − 21/50)]`.
* **P-30 (bullet misalignment cascades into nonsense error reports).**  Two *content* mistakes in the
  first draft — the `s = 1` branch of obligation A contained obligation B's derivation and vice
  versa — did not surface as "wrong goal"; they surfaced 20 lines later as a `rw` error whose printed
  goal belonged to a different bullet, plus three spurious "No goals to be solved" reports upstream.
  When Lean's error locations and printed goals stop agreeing with the line numbers in the file, the
  fault is almost always an earlier tactic that failed and desynchronised the `·` bullets; fix and
  recompile rather than chasing the reported line.
* **P-31 (`lintegral_prod_mul` needs `SFinite`, and the instance is not found by unification).**
  `∫⁻ z, f z.1 * g z.2 ∂μ.prod ν = (∫⁻ x, f x ∂μ) * ∫⁻ y, g y ∂ν` (`Measure/Prod.lean:1076`) is the
  whole Fubini step, but its *proof* needs `SFinite` on both factors and typeclass search does not
  reach `isProbabilityMeasure_gammaMeasure` on its own.  Provide it explicitly:
  `have hprobα : IsProbabilityMeasure (gammaMeasure α 1) := isProbabilityMeasure_gammaMeasure hα one_pos`.
  Use `have`, not `haveI` — the goal is a proposition, and `haveI` trips `linter.style.haveILetI`.
* **P-32 (Markov: prefer `meas_le_lintegral₀` to `mul_meas_ge_le_lintegral`).**
  `mul_meas_ge_le_lintegral hf ε : ε * μ {x | ε ≤ f x} ≤ ∫⁻ a, f a ∂μ` is the shape you want, but at
  `ε = 1` it leaves `1 * μ … ≤ ∫⁻ …` to be cleaned up and cannot be used directly on a *set*
  characterized by an implication.  `meas_le_lintegral₀ (hf : AEMeasurable f μ) {s} (hs : ∀ x ∈ s, 1 ≤ f x) :
  μ s ≤ ∫⁻ a, f a ∂μ` (`MeasureTheory/Integral/Lebesgue/Markov.lean:66`) is the right entry point:
  it takes the pointwise `1 ≤ f x` on the set as a hypothesis, which is exactly how a Chernoff step
  is stated.  That lemma is present in Mathlib even though `meas_ge_le_lintegral` is not.
* **P-33 (the Chernoff event inclusion holds only *a.e.*, and Mathlib has no Gamma support lemma).**
  The step "`X ≥ t` iff `G(1−t) ≥ Ht`" is used as an inclusion of sets, but
  `{p | t ≤ p.1/(p.1+p.2)} ⊆ {p | 0 ≤ p.1(1−t) − p.2·t}` is **false** pointwise: when
  `p.1 + p.2 < 0` the division by a negative flips the inequality.  (In the *lower*-tail direction
  it fails at `p.1 = p.2 = 0` instead, where `0/0 = 0`.)  The product measure does not see those
  points, but to say so one needs `gammaMeasure a r (Iio 0) = 0`, which **Mathlib does not have** —
  there is no support lemma for `gammaMeasure` at all.  It is extracted from the definition
  (`withDensity_apply` + `gammaPDFReal = 0` off `[0,∞)` + `setLIntegral_congr_fun`); see
  `TSDPP.gammaMeasure_apply_Iio_zero`.  Corollary for statements: any future lemma of the form
  "`X ∈ A` iff `(G,H) ∈ B`" must be stated through the *null set*, not as a set inclusion.
* **P-34 (`linter.unusedVariables` ignores identifiers that occur only inside a tactic hint list).**
  `by nlinarith [hu, ht]` and `by linarith [hv, ht1]` do *not* register `ht`/`ht1` as referenced, so
  a genuinely-used hypothesis is reported as unused.  Routing it through a `have` whose **term**
  mentions it fixes the warning: `have h1mt : (0:ℝ) < 1 - t := sub_pos.mpr ht1` then
  `nlinarith [hv, h1mt]`.  Do not "fix" this by deleting the hypothesis — the warning is about the
  proof term, not about the statement.
* **P-35 (`Set.setOf_or` is deprecated).**  Use `Set.ofPred_or`.  Likewise `push_neg` is deprecated
  in favour of `push Not`.  Both still elaborate, so they surface as warnings rather than errors.
* **P-36 (`setLIntegral_zero` does not exist).**  After `setLIntegral_congr_fun` has rewritten the
  integrand to `0`, close with `simp`.  Guessing `setLIntegral_zero` from `lintegral_zero` /
  `setIntegral_zero` costs a round trip.
* **P-37 (an unused hypothesis often means the statement is weaker than it needs to be — and here
  that strength was exactly what the second half of the proof needed).**  `gammaMeasure_prod_meas_le`
  was first stated with `(hu : 0 < u) (ht : 0 < t)`, because the *proof* derived `-(u*t) < 1` from
  `u, t > 0`.  But the Markov step only needs `0 ≤ y → 1 ≤ exp y`, which holds for **either sign** of
  `u` — the event `{0 ≤ u * (…)}` automatically selects the correct half of the line when `u < 0`
  rather than being vacuous.  So `0 < u` was never load-bearing: replacing the pair `(hu, ht)` by the
  two finiteness conditions `u(1-t) < 1` and `-(u*t) < 1` gives a strictly stronger lemma, and that
  extra strength is precisely what the *lower* tail needs (it is the same statement at `u := -v`).
  **Lesson: after a proof closes, re-read which hypotheses were actually consumed.**  The
  `linter.unusedVariables` warning is the cheapest available probe for this, and "delete the
  hypothesis" is usually the wrong repair — here the right one was to change what the hypothesis
  *was*, which turned two proofs into one.

* **P-38 (a wrong *parameter change* is invisible to every gate, and the only defence is a numeric
  check *before* the identification is used).**  GAP-2a defined the union-bound split by
  `s = δ/(δ + (1−μ)/μ)` instead of `s = δ/ρ`.  Consequences, in escalating order of seriousness:
  *(i)* two closed forms that are in fact exact to `1.5e−14` appeared to disagree with brute-force
  Chernoff optima by factors up to `10^193` at five `(α,β)` pairs — the *symptom* that exposed it;
  *(ii)* an entire ceiling estimate (`0.884097`, then a "corrected" `0.882745`) was computed from a
  quantity that was not the paper's;
  *(iii)* had the Lean development been written against the wrong `s` first, **every proof gate
  would have passed**: `lake build` green, `#print axioms` a subset of `{propext, Classical.choice,
  Quot.sound}`, `scan_forbidden.py` clean.  A wrong change of variables yields a *well-typed
  theorem about the wrong object*, and no proof-checking discipline can detect that — the statement
  is not what was intended, but it is provable.
  **Lesson: the numeral in a parametrisation is a claim about the paper, not an algebraic
  convenience, and it must be discharged numerically at *one concrete point* before anything is
  built on top of it.**  This is P-22 one level up (see the GAP-2a correction block): P-22 says a
  parametrised identity checked at a fixed point proves nothing; P-38 says an unchecked
  parametrisation proves nothing at *any* point, and passes CI while doing so.  The prose-and-Lean
  split in `CLAUDE.md` exists for exactly this: gate (A) — the informal argument — is the only
  place this class of error can be caught.

* **P-39 (a sweep over arbitrary *parameters* tests an identity; only a sweep over the *witness*
  tests the hypotheses — and a "FAIL" from the first kind does not mean the mathematics is wrong).**
  The `u`/`v` substitution identities of GAP-2e were checked on a grid of 7 `(α,β)` pairs × 3 values
  of `s` chosen *freely*.  The identities held to `1e−61`.  But the same sweep reported
  `v > 0 : False` at `(α,β,s) = (0.5, 3, 0.2)` and `(0.2, 5, 0.05)` — and the correct reading is
  *not* "the formula is broken".  Those are precisely the points where `ρs > 1`, i.e. `s` values
  that lie **outside the only regime where `v` is defined**.  The sweep had been asked a question
  the witness is never asked: the witness in regime 1 is `s = 29/(50ρ)`, which forces `ρs = 29/50`
  *identically*, so the failing points are unreachable.
  Re-run against the witness over 2000 log-spaced `ρ ∈ (29/50, 1000]`: zero violations, all nine
  hypotheses.  The same lesson applies to the `ρ = 29/50` endpoint, where `s = 1` makes `1 − s = 0`
  and `u` undefined — the boundary belongs to regime 2, and a grid that straddles it will divide by
  zero rather than report anything meaningful.
  **Sweep targets must be drawn from the same set the proof quantifies over.**  For an identity,
  that set is "all parameters where both sides are defined"; for a hypothesis, it is "the witness,
  and nothing else".  Conflating them manufactures false alarms, and — worse in the other
  direction — a free sweep can *certify* hypotheses the witness never satisfies.
  This is P-22's dual: P-22 says a fixed point does not prove a parametrised identity; P-39 says a
  parametrised sweep does not validate a witness.

* **P-40 (`Kernel.traj`'s index type is `↥(Finset.Iic n)`, not `Set.Iic n`).**  From the GAP-7
  probe (peer session, `Scratch/ProbeTraj.lean`; signatures re-verified here against the vendored
  tree).  `ProbabilityTheory.Kernel.traj` has domain `Π i : Iic a, X i`, and because
  `Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean:86` does `open Filter Finset Function …`,
  that `Iic` resolves to **`Finset.Iic a` coerced to a type** — not `Set.Iic a`.  The two are easy
  to conflate when transcribing from a reference repository, and the mismatch surfaces as a type
  error at the instantiation site rather than anywhere informative.  Check the `open` line before
  copying a signature.
* **P-41 (`Filtration.natural` needs a *topology* on the state space, and Lean will not synthesise
  the four dependent instances for you).**  Also from the GAP-7 probe.
  `Mathlib/Probability/Process/Filtration.lean:395` requires, per coordinate,
  `[∀ i, TopologicalSpace (β i)]`, `[∀ i, MetrizableSpace (β i)]`, `[∀ i, MeasurableSpace (β i)]`,
  `[∀ i, BorelSpace (β i)]`, plus `[Preorder ι]`, and it takes the measurability as an *argument*
  (`hum : ∀ i, StronglyMeasurable (u i)`).  Attaching a topology (weak topology, here) to a belief
  space is real work, and the failures are `failed to synthesize instance of type class
  ℕ → TopologicalSpace T` — three lines of noise for one missing `fun _ => inferInstance`.
  **Resolution taken: a hand-written filtration.**  Three lines, no topology, and valid for any
  `[MeasurableSpace S]`:
  ```lean
  noncomputable def handFiltration : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → S)) where
    seq i := ⨆ j ≤ i, MeasurableSpace.comap (fun ω : ℕ → S => ω j) inferInstance
    mono' _ _ hij := biSup_mono fun _ => ge_trans hij
    le' _ := iSup₂_le fun j _ => (measurable_pi_apply j).comap_le
  ```
  The peer records — and **did not prove** — that this `seq` body is verbatim the body of
  `Filtration.natural` (`Filtration.lean:396`, `seq i := ⨆ j ≤ i, MeasurableSpace.comap (u j) (mβ j)`),
  so the two should be *definitionally equal* in the Borel case.  That equality is **not** claimed
  here; it is recorded as an unproved observation, which is where it belongs.

* **P-42 (the deprecation sweep continued: `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`).**  Hit while
  unfolding a `private def goodSet : Set (ℝ × ℝ)` at a hypothesis.  `simp only [goodSet,
  Set.mem_setOf_eq] at hp` still elaborates but emits `warning: 'Set.mem_setOf_eq' has been
  deprecated: Use 'Set.mem_ofPred_eq' instead`, which fails a zero-warning gate.  Same family,
  same session: `Set.diff_univ` → `Set.sdiff_univ` and `Set.compl_eq_univ_diff` →
  `Set.compl_eq_univ_sdiff`.  Extends P-35; the deprecation surface of `Data/Set` is larger than
  P-35 suggested, and *every* renamed lemma is warning-only, so the gate that catches it is the
  warning counter, not `#check`.
* **P-43 (an `instance` whose head is a `noncomputable def` is invisible to typeclass search, even
  though it is definitionally true).**  `SFinite (gammaMeasure β 1)` is *not* synthesised, although
  `gammaMeasure a r` is `volume.withDensity (gammaPDF a r)` and
  `Measure.withDensity.instSFinite` (`Measure/WithDensity.lean:638`) concludes exactly
  `SFinite (μ.withDensity f)`.  Cause: the argument of the class is unified at `.instances`
  transparency, which does not unfold a plain (non-instance) `def`; `rw [gammaMeasure]` *inside* a
  `Prop` goal does.  Two transcriptions that do work:
  `example (β : ℝ) : SFinite (gammaMeasure β 1) := by rw [gammaMeasure]; infer_instance` and the
  term `SFinite (volume.withDensity (gammaPDF β 1))`.  This is P-31 one level down: P-31 says search
  does not *reach* `isProbabilityMeasure_gammaMeasure` (`have`-bind it); P-43 says search cannot
  even *enter* the definition, so the instance has to be declared — here as a top-level
  `instance instSFiniteGammaMeasure (a r : ℝ) : SFinite (gammaMeasure a r) := by rw [gammaMeasure]; infer_instance`.
  `Measure.prod_prod` needs it for its **second** factor only, which is why the error surfaced on
  `gammaMeasure β 1` and not on α.
* **P-44 (`linter.style.haveILetI` fires on *any* `haveI`/`letI` whose main goal is a `Prop` — so
  it is not safe to `haveI`-bind the instances a `Prop` proof needs).**  `Mathlib/Tactic/Linter/HaveILetI.lean`
  tests only `isProp (← getMainTarget)` and then suggests `have`.  The linter's premise ("proof
  irrelevance makes inlining irrelevant") forgets that `haveI` also *registers the local as an
  instance*.  Verified in this file: `have hα' : IsProbabilityMeasure (gammaMeasure α 1) := …`
  is picked up by instance search for `measure_univ`, because Lean 4's `synthInstance` considers
  every local hypothesis whose type is a class.  So the repair is genuinely `have`, not
  `set_option linter.style.haveILetI false` — and it must be applied consistently, because the
  warning fires in every `Prop`-valued lemma that needs an instance.
  This supersedes the remark in P-31 (`use have, not haveI`) with the reason and the scope.
* **P-45 (a `calc` step ending in a set-builder swallows the next line, and the error names happen
  to be about `Bool`).**  In
  ```lean
  calc ((gammaMeasure α 1).prod (gammaMeasure β 1)) {p : ℝ × ℝ | p.2 = 0}
      + ((gammaMeasure α 1).prod (gammaMeasure β 1)) badSet := measure_union_le _ _
  ```
  the `| p.2 = 0` body extends over the line break, and the reported errors were
  `invalid 'calc' step, left-hand side is true : Bool` and
  `unexpected token '_'; expected ')', ',' or ':'`.  `true : Bool` is the numeral `1` whose type was
  left undetermined by the mangled parse; nothing in the message mentions sets.  Fix: parenthesise
  every set-builder that is the last token of a line — `({p : ℝ × ℝ | p.2 = 0})`.  Corollary of
  P-30 in the other direction: when the printed goal/error names a type that cannot occur
  (`Bool` in a measure-theory proof), suspect the *parser*, not the elaborator.
* **P-46 (`linarith` cannot consume a goal of the form `p ∈ {p | P p}`, and `Or.inl` does not
  beta-reduce past the outermost `∪`).**  Two failure modes with the same root — relying on
  definitional unfolding where the tactic only does a syntactic comparison.
  *(i)* `refine Or.inl ?_` leaves the goal `p ∈ {p | p.2 = 0}`; `linarith` reports
  `linarith failed to find a contradiction … ⊢ False` even with `p.2 ≤ 0` and `0 ≤ p.2` both in
  context, because it looks for a relation at the head of the target and finds `Membership.mem`.
  Repair: `have h4 : p.2 ≤ 0 := by linarith` (a real `≤`) then `exact le_antisymm h4 h3`.
  *(ii)* For `badSet := s₁ ∪ s₂ ∪ s₃`, `exact Or.inl h1` with `h1 : p.1 < 0` fails — the goal
  whnfs one step to `(p ∈ s₁ ∪ s₂) ∨ p ∈ s₃` and the left disjunct is *not* reduced further, so the
  expected type printed is the whole `p ∈ s₁ ∪ s₂`.  Repair: `exact Or.inl (Or.inl h1)` (nest the
  constructors to match the association of `∪`, which is `(s₁ ∪ s₂) ∪ s₃`).
  Also in this family: `Ici_union_Iio` has an *implicit* `{a}`, so it cannot be applied to
  `(0 : ℝ)`; when the rewrite target is `univ` there is nothing to infer `a` from and one must
  write `Set.Ici_union_Iio (a := (0 : ℝ))`.  And `zero_le _` fails with
  `Function expected at zero_le` when the expected type already fixes its implicit argument —
  `bot_le` is the robust spelling for `0 ≤ μ s` in `ℝ≥0∞`.
* **P-47 (`MeasureTheory.Measure.ext_of_Ici` is in the `MeasureTheory.Measure` namespace).**
  `#check @MeasureTheory.ext_of_Ici` is an unknown identifier even though the declaration sits in
  `Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean` under an `open MeasureTheory`
  banner — the file opens `namespace MeasureTheory.Measure` at line 441.  Likewise `measure_union`
  is `MeasureTheory.measure_union` (not `Measure.measure_union`) and takes its `MeasurableSet`
  argument on the **second** set: `measure_union (hd : Disjoint s₁ s₂) (h : MeasurableSet s₂)`.
  Cheap probe: `#check @Name` for every lemma read out of the vendored tree (P-15's lesson applied
  to names rather than oleans).

* **P-48 (in a parameter substitution, the intermediate inequality is not the endpoint inequality —
  and the one handed to you can be the wrong one, while still being *true*).**  Provenance: the
  `8 → 100/11` radius substitution of task #12.  The prescribed route for `2√((100/11)x) ≤ 7√x` was
  `Real.sqrt_le_sqrt` on `(100/11)x ≤ 49x`, i.e. `100/11 ≤ 49` — true (`100 ≤ 539`).  But the goal
  needs `√((100/11)x) ≤ (7/2)√x`, i.e. `100/11 ≤ (7/2)² = 49/4 = 12.25`.  With the prescribed `≤ 49`
  one gets `√(K₀x) ≤ 7√x`, hence only `2√(K₀x) ≤ 14√x` — off by exactly the factor `2` that sits
  *outside* the radical.  **Cause**: `49 = 7²` is the square of the constant *after* the outer `2`
  is folded in (`2·(7/2) = 7`), so the comparison inside the radicand must be against `(7/2)²`, not
  `7²`; folding the outer `2` the wrong way is a factor-4 error in the radicand bound.  Here the
  mistake is *caught* — `linarith` prints the goal `7 * √x < 2 * √((100/11) * x)` and fails — which
  is the benign case.  **The dangerous repair is to weaken the statement to `≤ 14√x`**: that is
  provable, passes `lake build`, passes `#print axioms`, passes `scan_forbidden.py`, and raises the
  final rate constant from `8` to `15`.  That is P-38's failure mode — a well-typed theorem about
  the wrong constant — reached *through* a numeric check that passed, because the endpoint check
  `2√(100/11) = 6.030227 ≤ 7` is about a *different* inequality from the one the proof uses.
  **Rule: after a parameter substitution, re-derive every inequality in the chain from the goal and
  numerically check each intermediate bound, not just the endpoint.**  (`2√(100/11) ≤ 7` ✓,
  `100/11 ≤ 49/4` ✓, `2√(100/11) + 1 = 7.0303 > 7` ✗ for the old constant, `2√(100/11) + 1 ≤ 8` ✓ —
  the four checks disagree at the third, which is the one that moves the numeral.)
* **P-49 (`ring` cannot see through `√`: a producer/consumer pair must agree on the *syntactic*
  shape of a radicand).**  Provenance: the task-#12 substitution in `Theorem2.lean`.  The bridge
  `hcomm` in `theorem2_concrete` relates `theorem2_withTail`'s RHS `L * (2 * √((100/11) * m * logT / η))`
  to `rate_core`'s LHS `2 * L * √((100/11) * m * logT / η)` — a pure reassociation, so `ring` should
  close it.  It does **only** because both radicands are the *same term*.  `ring` treats `√X` as an
  opaque atom with no congruence rule for `Real.sqrt`, so `√((100/11) * (m * logT / η))` and
  `√(((100/11) * m) * logT / η)` are *distinct atoms*, and `ring` fails on a goal whose two sides are
  propositionally equal in any field.  **Symptom, and the reason it is logged:** the first error is
  `The ring tactic failed to close the goal` at the `hcomm` line, and the *informative* error is one
  line later — `Type mismatch: h40 has type 2 * ↑L * √(100 / 11 * ↑m * logT / η) but is expected to
  have type 2 * ↑L * √(100 / 11 * (↑m * logT / η))`.  The `ring` failure is only the shadow;
  debugging it directly costs a round trip.  **Fix**: pin the associated form once, in the declaration
  whose *statement* is the interface (`rate_core` uses the left-nested
  `(100/11) * (m : ℝ) * logT / η`, matching `theorem2_withTail`), and keep the `Z`-abbreviated
  internal steps in terms of the `set` so the internal algebra is untouched.  Corollary of P-16
  (defeq diamonds that `simpa` cannot cross) in the other direction: when two terms are "the same" to
  a mathematician but not to the elaborator, the **statement** is where the normal form gets fixed,
  not the proof.

* **P-50 (a *value* attributed to a declaration *by name*, where the name is right and the value is
  stale).**  Provenance: `FIDELITY.md` §1 and §4, found by a peer session and confirmed
  independently.  Six sites in `FIDELITY.md` read ``|BR| ≤ K·7·√(L³T log T/η)`` with an explicit
  attribution — "as the Lean theorem `TSDPP.theorem2_concrete`", "**Lean theorem** —
  `TSDPP.theorem2_rate`" — while both declarations state `8` (`Theorem2.lean:156` concludes
  `|BR| ≤ K * (8 * Real.sqrt …)`, `theorem2_rate` concludes `(8 * (C^2/2 + (2C^2+2CD+C))) * …`).
  The §3.4 substitution changed the *consumer* (`Rate.lean` 21:54, `Theorem2.lean` 21:55) and left
  the *consumer's documentation* behind (`FIDELITY.md` 21:37), so the doc is older than the code it
  describes — the ordinary "changed the consumer, forgot its documentation" shape, but with a
  distinguishing feature: **`grep` for the declaration name finds nothing wrong, because the name is
  correct.**  What is false is only the numeral printed next to it.  **Why no gate sees it:** the
  `8` appears nowhere in the Lean source of `FIDELITY.md`, so `lake build`, `scan_forbidden.py` and
  `check_axioms.sh` are all blind to it; §4 itself says its bridge step is "carried out by hand", so
  there is not even a Lean statement to disagree with.  A plausible-but-stale numeral in prose is
  invisible by construction.  **Fix**: when a constant changes, grep the *numeral* across the docs
  (`grep -rn 'K · 7\|7 · √\|7K'`), not the declaration name, and reconcile every hit against the
  declaration — and keep the old numeral only where the sentence explicitly labels it as the
  *paper's* (`FIDELITY.md` lines 265, 448 — "the paper's `2L√(8Z) + B ≤ 7√(L⁴Z)` at its radius
  `√8`" — are correct and must **not** be changed).  Corollary of the `cards/L5.md` lesson ("read the
  card, not the code") in the opposite direction: there, prose was trusted over code; here, prose
  quoted code by name and got the value wrong.  **The discipline in both directions is the same —
  a name is not a value; re-read the declaration.**  The conclusion survives (`8K'η^{−1/2}` still
  gives `O(√(L³T log T))`), so this was an attribution error and not a false claim.

* **P-51 (a proposition that *spans two files* is invisible to every single-file check — the hardest
  member of the P-50 family).**  Provenance: `Decomp.lean`'s module header says of `hdecomp` — the
  sentence reading "This is the former `hdecomp` hypothesis, discharged" — while `Theorem2.lean`'s
  header, in the bullet listing `hdecomp`/`hper`, says their proof is "Lemma 3 + Lemma 4 of [28],
  quoted by the paper and ***not* reproved there** (GAP-1)".  Both files are
  internally coherent; a reader of either gets a self-consistent — and *opposite* — impression of
  what the artifact proves.  The proposition under judgement ("is `hdecomp` reproved?") is not
  localised in any one file, so `lake build`, `scan_forbidden.py`, `check_axioms.sh`, and even a
  correct `grep` of the *right* name all pass.  This is strictly harder than P-50: P-50 is at least
  in principle catchable by a better single-file check (grep the numeral, not the name); here the
  search space is the *cross-product* of files and no per-file pass can reach it.  **Rule: any
  assertion about "what this artifact proves" that involves more than one file must come with an
  explicit cross-file consistency check, or it is unverifiable in principle — not merely unchecked.**
  **Scoping, not deletion, is the repair.**  That header bullet is not simply stale: `theorem2_rate`
  takes `hdecomp` *by design* — it is the general statement, with `(BR : ℝ)` abstract and
  `hdecomp : BR = ∑ l ∈ range m, episodeRegret l` a premise — while `theorem3_rate` is the
  *instance*: it has no `BR` and no `hdecomp`, its conclusion sums `r s` over `range (m * L)`, and
  its proof *calls* `theorem2_rate` at `BR := ∑ s ∈ range (m * L), r s`, discharging `hdecomp` by
  `regret_decomp_episodeOf r m L`.  So the accurate status
  is "`hdecomp` is a hypothesis of the general form and is discharged in the instance form";
  deleting the sentence would strip the general form of its premise documentation.  **Note the
  dependency direction**, which the two theorem names invite a reader to get backwards: the concrete
  `theorem3_rate` *calls* the general `theorem2_rate` — the instance is a corollary, not the source.
* **P-52 (`grep` answers a question about *text*, not about the proposition — and a pattern can
  silently shrink its own search space).**  Provenance: the `hdecomp`/`hper` reconciliation
  (`Theorem2.lean`), plus the audit-count error.  Three sub-forms, all observed:
  (i) **wrong place** — the fact is in `Regret.lean` and the search was in `Theorem2.lean`;
  (ii) **the pattern encodes the answer** — `sed -n '222,231p' … | grep -o "hper\|hdelta\|hηl\|hB0\|hBle\|hdecomp"`
  returns exactly those five, and was reported as "five remaining hypotheses" when the true count is
  nine; the alternation *is* the conclusion, so the command cannot falsify it;
  (iii) **regex semantics narrow the space without erroring** — `\b7\b` cannot match `7K'`, because
  `7` followed by a word character has no word boundary, so a sweep for the stale numeral reports
  "clean" while the site it was written to find is still there.  In (iii) the tool is *correct* and
  the *question was wrong*, which is the dangerous case: there is no error message to notice.
  **Rule: before believing a negative grep, state in words the proposition being tested and check
  that the pattern matches it — in particular, that the pattern does not contain any of the
  conclusion.**  Failing that, grep for something the answer cannot contain (here: every occurrence
  of the *numeral*, with no name in the pattern at all).
* **P-53 (a label assigned without checking it is free — the task list is prose too, and no gate
  reads it).**  Provenance: task #14 was created as "Add traps P-48/P-49 to DESIGN.md".  When acted
  on, this file already contained **P-48** (the parameter-substitution trap), **P-49** (`ring`
  cannot see through `√`) and **P-50** (a value attributed to a declaration by name) — all three
  written by the agents working that path.  Had the task been executed as written, two of the three
  entries would have been duplicated under numbers already in use, and a *live cross-reference*
  would have been silently re-pointed: P-48 is cited from inside the register discussion **earlier
  in this same section** (the sentence "see P-48 for the version of"), above the trap list.  So
  P-48 was not merely a free number — it was a number something already pointed at.
  *(This entry cites its neighbours by trap number and by quoted sentence, never by line: it is the
  only way an entry about identifier fragility stays valid under the next insertion.  A peer session
  caught the first draft doing exactly what it warns against.)*  The trap number is a *shared
  mutable key*, and the task recording it was written from a session that had not re-read the
  file.  **Rule: an identifier that other documents cross-reference is allocated by reading the
  document, at the moment of writing — never from memory of what the numbering "was up to".**
  This is the same failure as P-50 with the roles swapped: there the *name* was re-read and the
  *value* was stale; here the *value* was re-read and the *name* was stale.

* **P-54 (three gates green over a file that does not compile — the exemption that had become a
  hiding place).**  Provenance: a peer session, reproduced here.  `TSDPP/BetaConcentration.lean` —
  a file sitting in the deliverable directory — failed to build:

  ```
  lake build TSDPP.BetaConcentration   ->  REAL EXIT=1
    :276 Tactic `rewrite` failed      :298 Application type mismatch
    :308 Tactic `rewrite` failed      :327 unsolved goals
    :333 Tactic `rewrite` failed      error: build failed
  ```

  (The peer's probe saw *twelve* errors and this one five: the writing agent was mid-edit and the
  file moved between the two probes.  A moving target is not a contradiction, but it does mean
  neither count should be quoted as *the* number.)

  Every gate was nevertheless green, each for its own reason:

  | gate | why it cannot see this file |
  |---|---|
  | `lake build TSDPP` | compiles only the root module's **import closure**; this module is deliberately outside it |
  | `check_axioms.sh` (audit) | prints verdicts for the names listed in `Audit.lean` — 67 at the time of this entry, 79 now — none of which is defined here |
  | `scan_forbidden.py` | matches forbidden **tokens**; an unsolved goal and a failed `rewrite` contain none |

  And the line that suppressed the one warning that *would* have fired is
  `IN_FLIGHT = {"TSDPP.BetaConcentration"}` — an exemption whose own comment already reads *"it is
  an **exemption**, not a hiding place — an exemption that outlives its card is itself a defect."*
  Nothing in the script compiled the exempted module, so at that moment the exemption **was** the
  hiding place its comment disclaimed, and the disclaiming comment sat three lines above.

  **This is worse than the scenario `scan_forbidden.py`'s own docstring describes** ("artifacts
  promoted into `TSDPP/` are scanned but never type-checked"): same mechanism, but the failure mode
  is a hard compile error rather than a `sorry` — and a `sorry` would at least have been caught by
  the token scan.

  **Rule: an exemption must be narrower than the check it exempts from, and must suppress exactly
  one verdict.**  "Exempt from the orphan rule" silently became "exempt from being compiled",
  because the exemption was written as a *set of module names* rather than as *one named check*.
  The general shape: a check defined by an allowlist is only as strong as the allowlist's
  maintenance, and a broken entry is indistinguishable from a legitimate one — both are just a
  string in a set.

  **Fix applied.**  `scripts/check_axioms.sh` now `lake build`s every module in `IN_FLIGHT` and
  fails on a non-zero exit, and separately fails if `IN_FLIGHT` names a module that does not exist
  (a stale exemption hides nothing today, but will hide the next file to take that name).  Verified
  by running the gate on the broken tree: it now exits `1` and names the module.

  **Two consequences worth stating.**  (i) The gate is legitimately red *during* in-flight work —
  that is the honest state, and the gate's message says so; it is the state at *delivery* that is
  fatal.  (ii) The gate must not be run concurrently with an agent's own `lake build`: two lake
  processes over one build directory can produce a spurious `object file does not exist`, so a red
  result obtained during someone else's build is not evidence.  *This is a genuine cost introduced
  by the fix and is recorded rather than hidden.*

  **[RESOLVED 2026-09-17 — trap P-65, mode (a).]**  The exemption is gone: `IN_FLIGHT` is now empty
  and `TSDPP.BetaConcentration` is imported by `TSDPP.lean`, so it is inside the root closure and is
  built and scanned like any other module.  It has its own `#print axioms` section in `Audit.lean`.
  Two follow-ups this entry did not anticipate: `check_axioms.sh` now *requires* every closure module
  to have at least one audited declaration, and that requirement has its own negative control — a
  gate rule with no deliberately-broken test is an assertion, not a check.  See P-65 for the other
  four failure modes found while hardening this one.

* **P-55 (`field_simp` cannot clear a denominator that ring-normalisation has made syntactically
  different from the hypothesis that proves it nonzero).**  Provenance: `TSDPP/BetaConcentration.lean`
  §2, the lower one-sample tail.  Goal: `1 - α(1-δ)/(α+β-δα) = (1 + (1-δ)/(β/α))⁻¹`.  `field_simp`
  clears into the form containing `(α - αδ + β)⁻¹`, and the hypothesis `hab : 0 < α + β - δ*α`
  no longer matches the normalised denominator — and `field_simp` cannot prove the new one nonzero,
  so the goal survives the tactic with an unsolvable inverse.  **Rule: when the denominator is a
  hypothesis's own expression, do not let `field_simp` renormalise it — compose
  `eq_div_iff`/`div_mul_cancel₀`/`div_div_eq_mul_div`/`inv_div` instead:**
  ```lean
  have hX : 1 - α * (1 - δ) / (α + β - δ * α) = β / (α + β - δ * α) := by
    rw [eq_div_iff hA, sub_mul, div_mul_cancel₀ _ hA, one_mul]; ring
  ```
  Cost: it blocked the whole file (5 errors) until the compositional form was found.

* **P-56 (a trailing `inv_inv` in a `rw` list after an earlier rewrite has already collapsed the
  double inverse → `Did not find an occurrence of the pattern ?a⁻¹⁻¹`).**  Provenance: same file,
  the two `hkey` blocks: `rw [Real.inv_rpow h.le, Real.rpow_neg h.le, inv_inv, ...]` — the earlier
  `Real.rpow_neg` had already produced `((1-δ/(1+δ))^(-α))⁻¹` whose `inv_inv`-redex the *previous*
  `inv_inv` consumed.  Fix: delete the duplicate `inv_inv`.  **Rule: a `rw` list is a *sequence*,
  not a set of desiderata; re-read the goal after each entry rather than appending the "obvious"
  normalisation twice.**

* **P-57 (`ring` fails where `ring_nf` succeeds on the α-cleared optimiser identities).**
  Provenance: the two numerator identities of §2 (`... = δ/(1+δ)` and `... = δα/(β-δα)`), which
  need `ring_nf`'s normalisation of nested divisions to close.  Cheap rule: try `ring_nf` first in
  goals that mix `⁻¹` with polynomial identities over a field.

* **P-58 (a set-membership hypothesis is not an inequality for `linarith`; and `not_lt` must be in
  the `simp only` set).**  Provenance: §4's `hsub`.  `intro p hp` gives `hp : p ∈ {p | s ≤ |…|}`,
  which `linarith` cannot consume — `simp only [Set.mem_ofPred_eq] at hp` first.  Turning
  `h : ¬ (p ∈ A ∪ B)` into the four usable inequalities needs *both* `not_or`/`not_le` **and**
  `not_lt` — with `not_lt` missing, `¬ p.2 < t₂` stays un-consumable and `linarith` reports
  "failed to find a contradiction" on a goal that is two `simp` lemmas away from closing.  Also:
  `Set.mem_setOf_eq` is deprecated — the current name is `Set.mem_ofPred_eq`.

* **P-59 (`IsProbabilityMeasure` transfer through `hmap`, and two linters that fire on the way).**
  Provenance: §3.  `have hprob : IsProbabilityMeasure (betaMeasure α β) := by rw [hmap]; infer_instance`
  and `IsProbabilityMeasure ((betaMeasure α β).prod (betaMeasure α β))` by `infer_instance`
  (probe-confirmed in `Scratch/BCProbe3.lean`).  Two linters: `haveI` on a *proposition* trips
  `linter.style.haveILetI` (use `have`), and the `hmap` hypothesis then trips the unused-variable
  linter if the instance is never consumed (consume it — the transfer *is* the use).  Related:
  the unused-variable linter counts the *elaborated term*, so a hypothesis used only as a
  `linarith` hint list is still "unused" if the step is derivable without it: in §5 `hr : 1 ≤ r`
  follows from `hrel : δ₁ ≤ r-1+δ` (for the `δ ≤ δ₁` regime) and the linter was right.  Prefix the
  binder `_hr`; positional application is unaffected.

* **P-60 (the arithmetic residual must be read off the reduction's *actual* output, not from a
  remembered form — the factor `2` is easy to double-count).**  Provenance: §5, this session.  The
  intended `hnum` was written `2 * (A^α + B^α) ≤ exp (-(11/100)·α·r²)`; the reduction actually
  yields `Pr ≤ 2·(μ(Ici t₁) + μ(Iio t₂)) ≤ 2·(A^α + B^α)` (the outer `2` is the exchangeability
  factor, and the four-set cover already spends one copy of each tail), so the correct residual is
  `A^α + B^α ≤ exp (-(11/100)·α·r²)` — the target's own `2·exp(…)` supplies the other factor.  Lean
  caught it only as an `ENNReal.ofReal_le_ofReal` type mismatch at the last `calc` step.  **Rule
  (same as P-38, one level up): compute the residual from the exact shape the previous step
  returns, and check the *direction and the constant factor* numerically before proving it.**

* **P-61 (a constant designed to be *tight* cannot be spent twice — and splitting an event into
  one-sided tails costs a factor `2` in the exponent).**  Provenance: §5 + the numeric scans of
  this session, and the reason the top-level target is still open here.  `TSDPP.unionWitness`
  certifies `c₀ = 11/100` for the *two-sample* difference; the union bound needs
  `A(δ₁)^α + B(δ)^α ≤ exp(-(11/100)αr²)`, and at the balanced optimum `δ₁ = δ = 29/50` the two
  factors give `-log A ≈ 0.1225`, `-log B ≈ 0.1247` (`ρ → ∞`): the witness's constant is the
  target's, i.e. it is *exactly* what the union bound has to re-consume, and there is no slack for
  the second tail.  Numerically `hnum` then holds only for `r ≤ 1.055` with `α ≳ 56` (one-sample
  shape) resp. `α·r² ≳ 11` (interpolated shape `δ₁ = r-1+δ`), leaving a scanned window
  (e.g. `ρ ≳ 20`, `r = 1`, `α ∈ (24,47)`) that *neither* the union bound, *nor* the trivial branch,
  *nor* one-sided Cantelli with the exact `Var = αβ/((α+β)²(α+β+1))` covers.  The window is an
  artefact of the method: at `ρ → ∞, r = 1` the true exponent is `≈ 0.25α` (two `Gamma(α,1)`'s at
  the `√α` scale) against the union's `0.1225α`.  **Rule: before spending a certificate constant as
  a per-branch margin, count the branches; and for a *difference* of two independent variables, a
  union of one-sided tails is not the sum of two one-sided rates — the joint (product-measure)
  Chernoff is a factor `2` better and is what the constant `11/100` was sized for.**

* **P-62 (three corrections, one source: a claim true on a restricted subset read as true on the set
  the proposition quantifies over).**  Provenance: this correction sweep, three rounds, each
  superseded; the numbers below were independently re-derived.  The prose is corrected in place at
  four sites — `lean4/TSDPP/BetaConcentration.lean`'s module header (the bullet ending "no refinement
  of the one-sample Chernoff bound closes the target below that `α`"), `cards/L5.md` (the paragraph
  "the obstruction is a theorem, not a numeric surprise"), `FIDELITY.md` (the paragraph quoting
  `sup_{s,ρ}[A(s)^α+B(s)^α]^{1/α} = 0.883997`), and `DESIGN.md` GAP-2b (the displayed
  `sup_{s,ρ} [A(s)^α + B(s)^α]^{1/α} = 0.8839970429`) — and the corrections there now only subtract.

  *Layer 1 — the original chain (false).*  The chain
  `A(δ₁)^α + B(δ₁)^α ≥ 2·(A(δ₁)B(δ₁))^{α/2} ≥ 2·0.883997^α` links a **true** AM–GM step to a
  **false** one: step 2 needs `A(δ₁)B(δ₁) ≥ 0.883997²`, and it fails for unbalanced splits — as
  `δ₁ → 0`, `A(δ₁) → 1` and `B(δ₁) → 0`, so `(AB)^{1/2} → 0` and `A^α+B^α → 1`.  The claimed bound
  sits *above* the true minimum: `min_δ (A^α+B^α)` is `1.0000` against the claimed `1.5629` at
  `α = 2`, and `0.18180` against `0.24586` at `α = 17`.  The threshold
  `α < log 2/(0.123302 − 0.11r²)` (`≈ 52` at `r = 1`) is therefore **not established** by it.

  *Layer 2 — the first replacement (false).*  It read `max(A(δ₁),B(δ₁)) ≥ m` with
  `m = inf_δ max(A,B) = 0.8839970429`.  That value is **`sup_ρ min_δ max`**, and
  `min_δ max(A_ρ,B_ρ)` **increases** in `ρ` — `0.5 → 0.603256`, `1 → 0.750000`, `2 → 0.819143`,
  `5 → 0.858599`, `10 → 0.871389`, `100 → 0.882745`, `→∞ → 0.8839970429` — so it is **not a lower
  bound at finite `ρ`**.  The replacement also wrote `hnum`'s two terms — `δ₁` inside `chernoffA`
  and `δ` inside `chernoffB`, independent of each other — as one and the same `δ₁`.

  *Layer 3 — the second replacement (false; the decisive one).*  Even taking the correct per-`ρ`
  infimum, the symmetric-slice bound is invalid for `hnum`.  `hnum` binds **two independent
  parameters** linked only by `hrel : δ₁ ≤ r−1+δ`; the diagonal slice `δ₁ = δ` therefore yields a
  **one-dimensional** infimum which is an **upper** bound of the **two-dimensional** infimum over the
  admissible set, not a lower bound.  That two-dimensional infimum **collapses to `0`** when
  `ρ ≤ r−1`: take `δ₁ → ρ⁻`, so `A(δ₁) → 0`, and `δ → 0`, so `B(δ) → 0`; then `hnum`'s left side
  tends to `0 ≤ exp(−(11/100)αr²)`.  So `hnum` is satisfiable for **arbitrarily large `r`**, and
  **there is no upper bound on `r` at all**: neither `r ≤ 1.058737` nor any `ρ`-dependent ceiling
  stands.

  A *third* correction, to this very layer, is recorded as **P-63** below: the collapse witnesses
  exhibited here were mostly on the vacuous side, and the sentence "satisfiable for every `r`" is
  true but must carry the qualification that the witnesses sit at event level `s → 1`.  Also
  retracted with layer 3: "on `ρ > r−1` the constrained infimum *is* `m(ρ)`" — the constraint is
  slack, so `A` may be evaluated at `r−1+δ` (counterexample in P-63).

  *Status.*  `c₀ = 11/100` is **[UNDERIVED — 常数依据待独立重导]**: its `α ≈ 52` ancestor is
  downstream of layer 1, and layer 3's uniformity argument gives no upper bound, so no positive
  argument for the constant is written here.  What the union-bound branch proves is exactly the
  conditional of `betaMeasure_prod_abs_sub_le_unionTail` — the target follows from `hnum` — and
  nothing about which `(ρ, α, r)` admit `hnum`.  The target is **not** proved.

  *One-line lesson.*  **All three errors share one source: treating "true on a restricted/symmetric
  subset" as "true on the set the proposition actually quantifies over".  The first two are
  quantifier/parameter mismatch; the third is optimisation-set mismatch.**

  **Rule.**  (a) A lower bound for a residual must be taken over the *whole* set the hypothesis
  quantifies over — a slice, a diagonal or a grid gives an upper bound of the true minimum, never a
  lower one.  (b) Name the parameter, not just the value: `sup_ρ min_δ max` and `inf_δ max` at fixed
  `ρ` are different objects.  (c) Before shipping a correction, test it against the same adversarial
  direction as the original: a correction written in the shape of the error it replaces inherits that
  error, and green gates do not read prose.  The same sweep also corrected a mis-stated companion
  quantity: `sup_{s,ρ}[A(s)^α+B(s)^α]^{1/α}` in GAP-2b and `FIDELITY.md` is `≥ 1` (it ranges over
  `δ → 0`), not `0.883997` — the object GAP-2b's calculation actually concerns is
  `sup_ρ min_δ max(A,B)`.

* **P-63 (vacuity check: an infimum collapse found on the set where the proposition has no
  content).**  Provenance: the layer-3 correction inside P-62 was itself refuted in the same sweep by
  the peer session, which noted that the witnesses for the collapse all sit in the empty-event
  region.  Both halves of that exchange are recorded, because the refutation is right and the
  proposed replacement ceiling is not.

  *The observation (correct, and sharper than stated).*  The conclusion of
  `betaMeasure_prod_abs_sub_le_unionTail` bounds `Pr(|X−Y| ≥ r·α/(α+β))`.  Since `X, Y ∈ [0,1]`,
  `|X−Y| ≤ 1`, so with `ρ := β/α` and `s := r/(1+ρ) = r·α/(α+β)` the **event level**,

      `μ{|X−Y| ≥ s} = 0`  ⟺  `s ≥ 1`  ⟺  `r ≥ 1+ρ`  ⟺  `ρ ≤ r−1`.

  The criterion is **nullity, not emptiness** (the peer's refinement): at the boundary `r = 1+ρ` the
  event `{|X−Y| ≥ 1}` is `{(0,1),(1,0)}` — non-empty, but null because `Beta(α,β)` with `α, β > 0`
  puts no mass on `{0,1}`.  Nullity is both the correct criterion and the weaker one, so nothing is
  lost; stating it as emptiness would over-claim the hypothesis the conclusion actually needs.
  P-62's layer 3 exhibits the collapse of the two-dimensional infimum under exactly `ρ ≤ r−1`.  **The
  collapse set and the null-event set are the same inequality** — not nearby, identical.  So every
  witness of the collapse is a witness on which the target is `0 ≤ exp(⋯)`, i.e. has no content.
  P-62's own witness list is affected: of the runs at `r = 1.1, 1.5, 2, 3, 5, 100, 1000` produced by
  the recipe `ρ = (r−1)/2`, every one with `r ≥ 1.5` was vacuous (`r=1.5`: `1+ρ = 1.5 ≤ 1.5`,
  boundary; `r = 5`: `1+ρ = 2`; `r = 1000`: `1+ρ ≈ 500`), and only the `r = 1.1`, `ρ = 10` run was
  non-vacuous — and that one was not the constrained optimum either (see below).  The *conclusion* of
  layer 3 survives (`hnum` is satisfiable for every `r ≥ 1`), but the collapse is **not** evidence
  that the union-bound method is strong at large `r`; it is strong only where the target is void.
  The paper's `r ≥ 1` is what the file writes as `_hr`; it constrains nothing here — the real
  parameter is `s`, and the collapse is bought by `s → 1`.

  *The replacement ceiling (wrong, retracted).*  The peer proposed that on `ρ > r−1` the constrained
  infimum *is* `m(ρ) = min_δ max(A(δ),B(δ))`, hence the criterion `−log m(ρ) ≥ c·r²`, hence
  `inf_ρ(−log m(ρ)) = −log 0.8839970429 = 0.1233016` as a **ceiling** on the achievable rate, killing
  `c = 1/8` (`√(0.1233016/0.125) = 0.993183 < 1`) and admitting `c = 11/100`.  Three defects:

  1. **The constrained infimum is not `m(ρ)`**, on either side of `ρ = r−1`.  The constraint is slack
     — `δ₁` may exceed `δ` by as much as `r−1`, so `A` may be evaluated at `r−1+δ`.  Counterexample,
     checked by direct substitution: `ρ = 10`, `r = 1.1`, so `s = 0.1` (far from vacuous).  The pair
     `δ₁ = 0.6`, `δ = 0.5` satisfies `hrel` (`0.6 ≤ 1.1−1+0.5 = 0.6`) and gives
     `max(A(0.6),B(0.5)) = max(0.861784, 0.814447) = 0.861784`; the true constrained infimum is
     `0.846523`.  Both are **below** `m(10) = 0.871389`.  The peer's proof sketch inverts a sign in
     the branch `δ ≥ δ* − (r−1)`: it asserts `A(r−1+δ) ≥ A(δ*)`, which by monotonicity of `A` needs
     `r−1+δ ≤ δ*` — the opposite of the branch hypothesis.  The counterexample lies in that branch.
  2. **`0.1233016` is a floor, not a ceiling.**  Layer 3's collapse drives the achievable exponent to
     `+∞`, so `−log m(ρ) ≥ 0.11r²` is not a necessary condition and `1/8` is **not** excluded by this
     method.  The rate grows with the event level: `r = 2` gives `0.4685` at `s = 0.9`, `0.9894` at
     `s = 0.99`, `4.4319` at `s = 1−10⁻⁸`; `r = 5` gives `0.3191 → 0.6460 → 2.8472`.
  3. Consequently the "which constant is reachable" question has no answer on this route: `11/100`
     is not derived, **and neither is `1/8` refuted**.  The `[UNDERIVED]` marker stands, for a
     different reason than the one proposed.

  *What is true, and the right shape of the statement.*  For a **fixed** cap `s ≤ s₀ < 1` on the event
  level there *is* a ceiling, and it diverges as `s₀ → 1`: `r*(s₀) = 6.159`, `8.554`, `12.138`,
  `20.460`, `40.187`, `61.073` at `s₀ = 0.3, 0.5, 0.7, 0.9, 0.99, 0.999`.  These are the largest roots
  of `G(r,s₀) = 0.11 r²` where `G(r,s) = −log r − ((r−s)/s)·log(r(1−s)/(r−s)) = −log A(r−1)` — the
  `δ → 0` branch of the constrained infimum, on which `v(r,s) = A(r−1)` to every digit computed
  (closed form verified against the exact crossing root-finder at `(r,s) = (10, 0.9)`, `(10, 0.99)`,
  `(40, 0.99)`).  They are `α → ∞` indicators, not theorems; finite `α` carries `log 2/α` slack.
  *(The values `8.5, 20.1, 36.3` first recorded here were grid-limited and the last was wrong:
  a coarse `s`-grid never reached `s = s₀` exactly, where the maximum is attained.)*  The honest
  sentence is therefore **no absolute ceiling, and whatever ceiling exists is bought entirely with
  vacuity.**

  *Sharpening (the peer's, accepted).*  Since every `c` is reachable as `s → 1`, `11/100` is not
  merely underived on this route — it is **undistinguished**: the reachable set of constants is
  `(0, ∞)` in the near-vacuous limit, so `11/100`, `1/8` and `1` stand in the same position.  A
  constant can only be meaningful relative to a bounded `s` — which the artifact does not supply.

  *One-line lesson.*  **Before concluding that a proposition is unbounded from the behaviour of a
  witness family, check that the family is not confined to the region where the proposition is
  vacuously true** — here, the inequality that makes the infimum collapse (`ρ ≤ r−1`) and the
  inequality that makes the event empty (`r ≥ 1+ρ`) are literally the same.

  **Rule.**  (a) For any concentration statement, compute the *event level* `s` (threshold ÷ the
  ambient diameter) and record it beside every witness; a witness with `s ≥ 1` proves nothing.
  (b) When a family of witnesses makes a left side collapse, check whether the collapse condition and
  the vacuity condition coincide before reporting the conclusion as a ceiling or as an absence of one.
  (c) A "no bound exists" claim needs witnesses that are *non-vacuous*; a "bound exists" claim needs a
  minimum over the full quantifier set, not over a slice of it.  (d) The two errors can coexist in one
  exchange and point in opposite directions — here the first falsified a *ceiling*, the second would
  have reinstated it.

* **P-64 (the artifact inverted the lemma's RANGE, not its constant — and on the range it chose the
  target is FALSE).**  Provenance: a direct numerical falsification sweep of the registered target,
  re-derived here from scratch by exact rational arithmetic.  This supersedes the framing in GAP-2b /
  P-62 / P-63, which all assumed the artifact and the paper differed only in a constant.

  The artifact states (module docstring of `BetaConcentration.lean`, and
  `betaMeasure_prod_abs_sub_le_unionTail`)

    `Pr(|X - Y| ≥ r·α/(α+β)) ≤ 2·exp(-(11/100)·α·r²)`,  `X, Y` iid `Beta(α,β)`, **`r ≥ 1`**,

  whereas the paper's Lemma 5 reads, verbatim (p. 9),

  > "If X has a beta distribution `Beta(α, β)` and Y is an independent copy of X, then, **for all
  > `0 ≤ r ≤ 1`**, we have `Pr(|X − Y| ≥ rE(X)) ≤ 2e^{−αr²/8}`."   (31)

  So there are **two** differences — the range and the constant — and they are not independent.
  **The artifact did not mistranscribe `1/8` into `11/100`; it inverted the range.**

  *The refutation.*  Exact rational arithmetic (private-denominator rationals, no floating point in
  the critical path; every row independently reproduced by 40-dps `mpmath` through the regularized
  incomplete beta, agreeing to all printed digits):

  | `(α, β, r)` | `Pr(\|X−Y\| ≥ rα/(α+β))`, exact | `c_eff` | vs `11/100` | vs `1/8` |
  |---|---|---|---|---|
  | (1, 100, 10) | 2.809651246898e−05 | 0.111730 | holds | **fails 3.77×** |
  | (2, 200, 10) | 8.606640056681e−09 | 0.096319 | **fails 15.43×** | fails 311× |
  | (5, 500, 10) | 3.658586854855e−19 | 0.086290 | **fails 1.4e5×** | fails 2.6e8× |

  with `c_eff := −log(LHS/2)/(αr²)`, the largest constant the data admit.

  "fails `N`×" is the plain ratio `LHS / (2·exp(−c·α·r²))`.  By the definition of `c_eff` it equals
  `exp((c − c_eff)·α·r²)` — the same number written two ways, not two conventions — so a reader can
  check the column either from the probabilities or from the constants.  At `(2,200,10)`:
  `8.6066e−09 / (2e^{−22}) = 8.6066e−09 / 5.579e−10 = 15.43`, and `e^{(0.11 − 0.096319)·200} = 15.43`.

  `(1,100,10)` refutes the *paper's* constant and `(2,200,10)` refutes the *artifact's* — the
  failures sit in different corners, so neither constant repairs the other.

  *The mechanism, verified independently.*  `betaMeasure_prod_abs_sub_le_unionTail` itself is a
  valid implication (its `r ≥ 1` hypothesis is inert, `_hr`), so at a point where its **conclusion**
  is false its **antecedent** `hnum` must be unsatisfiable.  It is: over the admissible set
  `0 < δ₁ < ρ`, `0 < δ < 1`, `δ₁ ≤ r−1+δ`, the infimum of `A(ρ,δ₁)^α + B(ρ,δ)^α` at `(2,200,10)` is
  `6.431e−7`, attained at the binding corner `δ₁ = r−1 = 9`, `δ → 0`, against the required
  `exp(−(11/100)·2·100) = 2.789e−10` — a **2305× miss**.  The optimal split is pinned by exactly the
  constraint `δ₁ ≤ r−1+δ`: with `δ → 0` (which the small lower tail demands) it reads `δ₁ ≤ r−1`.
  **`1 ≤ r` is therefore not an incidental hypothesis of that theorem; it is the price of the split.**
  For `r ≤ 1` the lower tail must be paid at `t₂ = μδ` with `δ ≈ 1−r/2`, where `B(ρ,δ)^α` is not
  exponentially small, and the method does not close at all.  The method's usable range and the
  statement's true range have disjoint interiors.

  *The paper's own usage is why the artifact inverted it.*  Eq. (33) sets
  `r_i^l = max{1, √(8 log T / α_i^l)} ≥ 1` and then applies Lemma 5 — **outside the lemma's stated
  range**.  The artifact inherited a live defect in the paper, not a typo.  On the paper's stated
  range the bound is safe with room: sweeping `α ∈ [0.5, 200]`, `ρ ∈ [0.1, 1000]`, `r ∈ [0.1, 1]`
  gives `min c_eff = 0.242848` at the box corner `(α,β,r) = (200, 200000, 1)`, i.e. **+0.118 above `1/8`**.  [Corrected 2026-09-18: this read `0.23838` at `(200,20000,1)`; that point's true value is `0.245510`, and `0.23838` is attained nowhere in the box.  See P-69.]  In the
  paper's *own* regime `r = √(8 log T/α)` the constant dies from `T ≈ 10⁵`: `(α,β) = (1,100)`,
  `T = 10⁶` gives `r = 10.513`, `c_eff = 0.10623 < 1/8` (and `< 11/100`).  **The paper's Lemma 5 as
  printed is true; the paper's application of it is not; the artifact formalized the application.**

  *What this does and does not change.*  It does not touch the reduction, nor the four `'`-forms, nor
  the Beta–Gamma work — `hnum ⟹ bound` remains correct.  It does mean (i) the registered target must
  be restated on `0 ≤ r ≤ 1` with the paper's `1/8`, and (ii) `hnum` is *not* "satisfiable for every
  `r ≥ 1`" as the header and `Audit.lean` currently say: it is satisfiable exactly where the bound
  holds, which by P-63 means the vacuous region `ρ ≤ r−1` plus only such non-vacuous region as the
  true exponential really covers.

  **Rule.**  (a) When formalizing a quoted lemma, record the **range** of its parameter next to the
  constant; a constant without a range is meaningless (this is the same lesson as P-63(b), arriving
  from the other direction).  (b) If a proof method closes only under a hypothesis, check whether
  that hypothesis is what makes the statement *easy* before adopting it — here the method needed
  `r ≥ 1`, and `r ≥ 1` is where the claim is false.  (c) An inequality used outside its stated range
  in the source is a defect of the source; if the artifact inherits it, mark it.

  **[EXTENDED 2026-09-17 — see P-67.  The witnesses above understate the problem.]**  They sit at
  `r = 10` with `ρ = 100`, which is outside the vacuous region but **off the curve Eq (33)
  prescribes**.  Evaluated on that curve — `r = max{1, √(8 log T/α)}` — the **paper's own `1/8` also
  fails**, in 5 of 6 sampled parameter tuples, including `α = 1, T = 10⁶` (the artifact's `11/100`
  fails there too).  P-64 establishes that the artifact's formalization is false; P-67 establishes
  that the paper's *use* is false on the paper's own settings.  The rules above are unchanged, but
  (a) should be read to include the *use site's* parameter curve, not just the lemma's stated range.


* **P-65 (five ways the audit gate could report green while checking nothing).**  Provenance: the
  hardening of `lean4/scripts/check_axioms.sh` (task #19).  The gate is the artifact's only
  machine-checkable evidence for `CLAUDE.md`'s "no `axiom`/`native_decide`/`unsafe`" rule, so a gate
  that silently checks less than it appears to is worse than no gate: it converts an open question
  into a false assurance.  Five distinct failure modes were found and closed.

  (a) **The exemption list.**  `IN_FLIGHT = {"TSDPP.BetaConcentration"}` excused a module from *both*
  the orphan check and the audit.  Its own comment already said the module "is *compiled* by the
  gate" — true, and irrelevant: compiling is not auditing, and the exemption meant twelve public
  declarations were checked by nothing while the gate printed `OK`.  `IN_FLIGHT` is now empty.  Note
  the exemption was self-justifying: the module was outside the root closure, so `Audit.lean` (which
  imports only `TSDPP`) could not even *name* its declarations.  This hole has now been hit five
  times (`KL`/`GammaMGF`, `BetaGamma`, the two promoted modules, the four quarantined to
  `Scratch/superseded/`, then `BetaConcentration`); §2's tree invariant is the durable fix.

  (b) **A comment can silently kill the whole gate.**  A `'` inside a comment in the `python -c '...'`
  block ends the bash single-quoted string at that byte, and the rest of the script is parsed as
  shell.  Result: `syntax error` — **exit 2 with no output**.  The tell is precisely the hazard: a
  bare non-zero exit with nothing printed looks like "red, investigate", and the natural next move
  (re-run it) reproduces the same nothing.  **Rule: any gate failure must print which check failed.
  Exit-without-output is its own bug, never a verdict.**

  (c) **A reporting regex that under-reports turns red into green.**  The axiom-extraction regex used
  the class `[A-Za-z0-9_.]`, which cannot match the trailing `'` in `'TSDPP.foo'' depends on axioms`.
  Every primed declaration (`betaMeasure_Ici_chernoff'` and the three siblings) matched *nothing* and
  was silently filed under "EMPTY axiom set" — i.e. the four declarations whose `hmap` discharge is
  the most delicate step in the module were the four the gate did not read.  `/` and `'` are
  legitimate characters in a Lean name; a name-matching regex must be written from the grammar, not
  from the sample that happened to be open at the time.  (Discovered by the audit agent while
  checking that the closure-coverage report matched the source.)

  (d) **Coverage measured per module is not coverage.**  The new check asserts *every module in the
  root import closure has at least one audited declaration* — a real improvement over "the module is
  in the closure" (five holes closed by (a)), but it is a floor, not the property.  It passes while
  30 of 109 public declarations remain unaudited (Belief 11, Lipschitz 6, Model 5, Ineq 3, Assembly
  2, Regret 2, Rate 1).  Stated here so the green line `21/22 modules … OK` is not read as "the
  closure is audited".

  (e) **The gate had no negative controls.**  A checker that has never been observed to fail is an
  assertion, not a check.  Five controls now exist (a `sorry` planted in a closure module, a module
  removed from `Audit.lean`, a stale allowlist entry, a non-existent allowlist entry, and an
  `IN_FLIGHT` entry naming a missing module), and each was observed to fire before the gate was
  trusted.  **Rule: a new gate check is not done until a deliberately broken input has made it
  fail.**

  Verified state after the hardening: `bash scripts/check_axioms.sh` exits 0, **79 declarations
  audited (3 with an empty axiom set), 23 source files scanned**, coverage `21/22` with
  `TSDPP.Basic` declaration-free and allowlisted.  Attribute (b) and (c) to the audit agent's sweep;
  they are reported here from its findings, not re-derived by me.

* **P-66 (a correction is itself a claim, and needs the same evidence as the thing it corrects).**
  Provenance: this session, and it is the cheapest near-miss recorded here.  While propagating P-64 I
  noticed the evidence table's "fails `N`×" column and computed `2e^{−22}` as `5.579e−9` instead of
  `5.579e−10`.  On that slip I concluded the column used an unstated "exponential ratio" convention
  that would read as a 10× overstatement to anyone recomputing it, and wrote a warning paragraph
  into **three** documents (`DESIGN.md`, `BetaConcentration.lean`, and a draft for `cards/L5.md`)
  telling readers not to trust the column's arithmetic.  The column was correct in all three.  What
  saved it was writing the "two conventions" out symbolically: `LHS / 2e^{−cαr²}` and
  `e^{(c − c_eff)αr²}` are the same expression by the definition of `c_eff`, so no convention
  question exists — an internal contradiction that forced a recheck of the arithmetic.

  **Rule: a correction is a claim like any other.**  It carries the same burden — recompute the
  number, or derive the identity, *before* writing prose about it, not after.  A doc-level correction
  is worse than the error it targets, because it arrives with the authority of the sweep that found
  it, and the three documents were about to disagree with the artifact's own correct evidence.
  Corollary, and the operational tell: **when a "finding" is that some number is off by a
  suspiciously exact power of ten, recheck the arithmetic first.**  The slip above was the
  diagnostic; the finding was mine.

* **P-67 (the bound fails on the paper's *own* parameter curve, against the paper's *own* constant —
  so the witnesses in P-64 were not the worst case, and the "small-`α`" corner is).**  Provenance: an
  independent verification session (peer, `lean-proof-ts-dpp-af`) raised the large-`r` regime; the
  numbers below are **my own re-derivation**, not its report, using a quadrature routine validated by
  reproducing P-64's three exact witnesses to 11 significant digits before it was applied here.

  P-64's witnesses sit at `r = 10` with `ρ = 100` — chosen to be clearly outside the vacuous region,
  but **not on the curve Eq (33) actually prescribes**, which is `r = max{1, √(8 log T/α)}`.  Walking
  the paper's own curve changes the picture qualitatively:

  | `α` | `β` | `ρ` | `T` | `r = max{1,√(8 log T/α)}` | `c_eff` | vs `11/100` | vs the paper's `1/8` |
  |---|---|---|---|---|---|---|---|
  | 1 | 50 | 50 | `10⁶` | 10.513 | 0.11182 | holds | **FAILS** |
  | 1 | 100 | 100 | `10⁶` | 10.513 | 0.10623 | **FAILS** | **FAILS** |
  | 1 | 50 | 50 | `10⁹` | 12.876 | 0.09289 | **FAILS** | **FAILS** |
  | 1 | 50 | 50 | `10¹²` | 14.868 | 0.08195 | **FAILS** | **FAILS** |
  | 2 | 100 | 50 | `10⁹` | 9.105 | 0.11021 | holds | **FAILS** |
  | 5 | 500 | 100 | `10⁹` | 5.758 | 0.13425 | holds | holds |

  **The paper's constant `1/8` fails in 5 of these 6 rows, at parameters Eq (33) itself produces.**
  This is a strictly stronger statement than P-64: not "the artifact's formalization of Lemma 5 is
  false" but "the paper's use of Lemma 5 is false on the paper's own settings."

  *Why the failure is worst at small `α`.* `r` grows like `√(log T / α)`, while `c_eff` falls in `r`.
  Large `α` keeps `r` small (row 6: `r = 5.76`, safe); small `α` drives `r` past the crossing.  The
  `r`-dependence is **sub-quadratic**, so `c_eff` decreases monotonically in `r` and crosses *any*
  fixed constant eventually: at `ρ ≈ 48` the measured exponents `−log(P/2)` are `105.5, 270.4,
  728.2` at `r = 10, 20, 36`, i.e. per-unit-`r` growth `10.6, 13.5, 20.2` against the claimed
  `0.11αr = 1.32r` per unit (`13.2, 26.4, 47.5`).  The mechanism is the one the paper's own
  `(1−x)^{β−1}` factor makes plain: past the quadratic (CLT) region the log-density is **near-linear**
  in the deviation, so the true exponent is near-linear in `r` while the claimed bound is quadratic.

  *What this does and does not change.*  It does not touch any Lean declaration — `hnum ⟹ bound` is
  still a theorem, and the artifact's four `'`-forms are still correct.  It means (i) the registered
  target is false even in the region a reader would call "the paper's actual use", and (ii) an
  attempt to repair by restating on `0 ≤ r ≤ 1` fixes a range the paper never uses.  See J-11.

  **Rule.**  When a bound's free parameter is *set by another equation in the same paper*, evaluate
  the bound **on that curve**, not on a convenient grid point.  P-64's witnesses were valid and the
  finding was real, but they understated it: the paper's own `r(T)` is where the guarantee lives, and
  it is the first place a reviewer will look.  A witness chosen off the parameter curve invites the
  reply "not in the regime we care about"; a witness on it does not.

* **P-68 (in the small-`α`/`β` corner, nothing but the density itself is a usable reference —
  including high-precision integrators).**  Provenance: the peer session's own methodology note,
  recorded here because it cost it real time and would cost the next attempt the same.  Its first
  scanner used a logistic substitution with `scipy.logsf` and was wrong by up to `0.11` at small
  `α`, `β` — and the error went in the direction that **hides violations**, i.e. it under-reported
  exactly the phenomenon being hunted.  The cause was not the special function (`betainc`'s two
  implementations agree to `1e-16`) but adaptive quadrature **missing a peak** after the
  substitution.  `mpmath`'s tanh-sinh was then used as ground truth and *also* missed peaks (off by
  `0.019` at `(0.05, 0.1)`), and was caught only by a `4·10⁷`-sample Monte Carlo.  The final form
  (adaptive `quad`, explicit breakpoints at both ends, variable change chosen so the peak is
  interior) agreed with Monte Carlo to `≤ 5.4e-4`.

  **Rule.**  A numerical method is not validated by *agreeing with a different numerical method* when
  both share the failure mode that matters (here: adaptive quadrature missing a narrow peak).  It is
  validated against something structurally different — here Monte Carlo, which cannot miss a peak
  because it samples the density directly.  **Corollary, and the reason this is a trap rather than a
  war story: check the *direction* of a numerical error before trusting a null result.** An error
  that inflates a bound hides violations; an error that deflates one manufactures them. The first
  kind turns "no violations found" into a false negative, which is the failure mode a falsification
  sweep exists to prevent.

* **P-69 (a numeric figure quoted without its grid is not evidence — four of them were wrong, and a
  verification agent found three).**  Provenance: an independent verification pass over J-11 and the
  P-64 tables, run precisely because those figures were about to be frozen into the design record.
  It reproduced the P-64 evidence table to `<1e-14` relative (all three `LHS` values, all three
  `c_eff` exactly) and confirmed the `hnum` mechanism (infimum `6.4309993e−7`, ratio `2305.457`,
  minimiser at `δ₁ → r−1`, `δ → 0`) — and then **refuted four other numbers**, three of which I
  re-confirmed myself on a second independent routine:

  | figure as recorded | measured | where it had propagated |
  |---|---|---|
  | `min c_eff = 0.23838` at `(200,20000,1)` | `0.245510` there | 6 files |
  | box minimum `0.23838` | `0.242848`, at the corner `(200,200000,1)` | 6 files |
  | exact route's worst ratio `0.0052` (≈190× slack) | `0.4530` (≈2.2× slack) | J-11(c) |
  | surrogate fails at `42 of 48` cells | `80 of 120` cells, worst `2.59×` | J-11(c) |
  | `Pr(X ≥ rμ) ≥ 1/2` for large `α` | `0.495857` at `α = 1000` — strictly *below* `1/2` | J-11(b) |

  What all four have in common: **they were computed on grids that no longer exist and were never
  written down.**  Not one could be re-run, because the grid was in a scratch script that was
  overwritten, and so the `range.py`/`feas3.py`/`fast.py` line of work is not reproducible even by
  its author.  The correct figures were obtained in minutes once the grid was stated explicitly.

  **Rule.**  A numerical figure enters a document only with (i) the exact grid or parameter list,
  and (ii) the routine that produced it, both in the repository — or it is marked *reported, not
  reproduced*.  **A number whose grid is unstated is not merely unverifiable; it is
  unre-falsifiable**, which is worse, because it cannot be corrected by the next attempt either — it
  can only be contradicted, as here.  Note the failure mode this shares with P-20 (a global claim
  checked on a truncated grid) and P-68 (an error whose direction hides violations): all three turn
  a null result — "the sweep found nothing" — into false confidence, and the common fix is to make
  the *scope* of the evidence part of the evidence.

  *Secondary, and worth stating: the verification agent's own first reading of Claim 1 said the
  `(1,100,10)` row was "wrong", because my brief to it said "row 1 exceeds the bound (fails by
  3.77×)" while the table row says the opposite (`holds` against `11/100`, fails against `1/8`).
  The table was right and the brief was sloppy. A witness table's per-row verdicts do not survive
  being paraphrased into prose — quote the row, do not restate it.*

* **P-70 (an asymptotic criterion quoted as if it were the exact threshold of the finite witness).**
  Provenance: `cards/L5-REFUTATION.md` §5, route R-F, written 2026-09-18 while justifying why the
  machine-checked refutation uses `(α, β, r) = (1, 100, 14)` and not the first `r` that fails.  The
  draft read: *"the failure needs `r + 1 > (11/100)·r²`, i.e. `r ≳ 9.6`"*.

  The criterion is the leading-order comparison — `(86/101)^B ≈ exp(−(r+1))` for large `B`, against
  `exp(−(11/100)r²)` — and it is a statement about `B → ∞`, not about `B = 100`.  At the actual
  `B = 100` it drops the factor `1 − (100/101)^100 ≈ 0.63`, worth `+0.46` in the exponent, which is
  enough to move the threshold by a whole integer.  The exact sweep of *this* card's own lower bound
  against the registered RHS gives the first failure at **`r = 12`**, with `r = 11` still holding by
  `1.64×` — so the quoted `9.6` is off by more than two units, and the correct value is available
  from the very table §5 already contains.

  **Rule.**  An asymptotic criterion is a statement about the limit; it may *motivate* a witness, it
  may not *justify* one, and if it appears at all it must be labelled asymptotic in the sentence
  that carries it.  The exact threshold of a finite witness comes from the sweep at that witness's
  parameters, and the sweep is the figure — so P-70 is P-69 entered through a different door: both
  replace an exact object with an approximation and then read the approximation as the object.

  *Secondary.*  The same edit quoted the slack of `(100/101)^100` against `3/8` as a bare "**0.85%**".
  There is no such number: the ratio `(3/8)/(100/101)^100` is `1.0143` (+1.43% on the denominator)
  while `(1 − (100/101)^100)/(5/8)` is `1.00846` (+0.85% on the denominator) — two different true
  figures for two different statements, one of which the draft mis-attributed.  A percentage without
  its numerator and denominator stated is the P-69 disease in miniature, and the card now quotes
  every slack as an explicit ratio.

Recorded so that a future attempt does not have to rediscover them.

### Two fidelity rules that must not be merged

Distilled from the `1/8 → 11/100` substitution (GAP-2b) and from the two places the artifact
**does** assert the paper is wrong: **GAP-6** (Eq (40)'s printed constant, §7) and **P-10** (Eq
(25)'s derivative at `x = 0`, in the trap list above).  These are different
claims with different obligations, and a correction sweep that carries one rule instead of two will
erase a live result:

| claim | form | what discharges it | where |
|-------|------|--------------------|-------|
| "the paper's printed step is **false**" | a counterexample | an explicit witness on which it fails | GAP-6 (Eq (40)'s constant), P-10 (Eq (25)'s derivative at `x = 0`), **P-64 (`1/8` on `r ≥ 1`)** |
| "the paper's constant is **unreachable by this method**" | an impossibility/ceiling | a proven upper bound on what the method can give | GAP-2b (`1/8` vs the union bound's ceiling `0.123302`), hence `c₀ = 11/100` |

`1/8` sits in **both** rows, and the reason is P-64: it is refuted *on the range the artifact
adopted* (`r ≥ 1`; witness `(α,β,r) = (1,100,10)`, ratio 3.77) and **not** refuted on the range the
paper actually stated (`0 ≤ r ≤ 1`, where the sweep minimum `c_eff = 0.242848` clears it by +0.118 (corrected 2026-09-18; see P-69)).
An earlier version of this table placed `1/8` in the right-hand row only and asserted it was "**not**
refuted"; that was true only before the range was checked, and it is exactly the kind of unqualified
statement this table exists to prevent.  Conversely GAP-6, P-10 and P-64 are **not** reachability
statements and must not be weakened into them — note P-64 refutes a *bound*, which is a different
object from GAP-2b's *ceiling of a method* (the two coexist: `11/100` may well be unreachable by
this method *and* false as a bound).  These claims sit close together in `FIDELITY.md` (§3.4 and
GAP-6/§7), which is exactly why the distinction is worth an explicit table rather than an understood
convention.

### GAP-1 — Bayesian-regret decomposition (paper's Lemma 3, 4; quoted from [28])
**Resolution taken**: *not* axiomatised, and *not* claimed.  `TSDPP.episodeRegret_le` and
`TSDPP.regret_le` take the per-round Bellman bound
`∀ t, |diff t| ≤ K·δ_t` and the decomposition `regret = Σ_t diff t` as **hypotheses**, and prove
everything that follows from them.  A reader who accepts [28]'s Lemma 3/4 gets Eq (38) for free;
a reader who does not can see exactly which step is being assumed.  This is strictly more honest
than an `axiom`, and it is what `CLAUDE.md`'s "不为闭合目标而引入公理" requires.

Still missing (for a future attempt): a Lean statement of
`J^{θ}_{π,1}(H₀) − J^{θ'}_{π,1}(H₀) = E_{θ,π}[ Σ_{t=1}^{L} (T^θ_π − T^{θ'}_π) J^{θ'}_{π,t+1}(H_{t−1}) ]`
(Eq (30)), plus the TS policy-mapping identity turning Eq (27) into Eq (28).
Blocking requirement: a probability space of trajectories `(A_1,X_1,…,A_L,X_L)` with the policy-induced
measure, and Bellman operators `T^θ_π` on `L¹` of that space. Neither exists in Mathlib.
Note: Eq (28) is *not* a triviality — it uses that `θ*` and `θ^l` are exchangeable given `Q^l`, so the
oracle term can be replaced by the algorithm's own value function. That exchangeability argument must be
formalized, not assumed.

### GAP-2 — Beta concentration inequality (paper's Lemma 5, quoted from [45])

Paper's Lemma 5: `X, Y iid Beta(α,β)`, `μ := E X = α/(α+β)` ⟹ `Pr(|X − Y| ≥ rμ) ≤ 2e^{−αr²/8}`.

**Status after this session: reduced to an elementary union bound, and *proved* at a constant
`c₀ = 11/100` replacing the paper's `1/8`.** The residual gap is a factor in the exponent, and
it is *quantified below to three decimal places*. It does **not** affect the paper's final rate:
Eq (40)'s geometric sum `Σ_l L·2e^{−c α^l}` converges for *every* `c > 0`, so `O(√(L³T log T))`
is unchanged. See GAP-2b.

#### GAP-2a — the reduction is exact and elementary

Set `ρ := β/α`, so `μ = 1/(1+ρ)`. The union-bound split is `δ > 0`; parametrise it by
`s := δ/ρ ∈ (0,1)` (equivalently `δ = ρs`), and define

  `A(s) := (1 + ρs)·(1 − s)^ρ`,   `B(s) := ρs·(1/ρ + 1 − s)^ρ`.

> **Correction (registered trap P-38).** An earlier revision of this section gave the relation as
> `s = δ/(δ + (1−μ)/μ)`. That is **wrong**, and it is not a harmless slip: it was introduced while
> *transcribing* a derivation, never numerically checked, and it silently made the two closed forms
> below appear to disagree with brute-force Chernoff optima (relative errors `0.498`, `85.7`,
> `7.3e193`, …) at five `(α,β)` pairs. The check that caught it — evaluate both sides at the same
> point *before* trusting an identification — is trap **P-22** ("a parametrised identity checked at
> a fixed point proves nothing") applied one level up: here the identity had never been checked at
> *any* point. With `s = δ/ρ` the two forms are exact to machine precision (§ below). Recorded
> because the failure mode is a wrong *parameter change*, which no amount of care inside the Lean
> proof would have caught: Lean would have proved a theorem about the wrong `s`.

**Derivation.** For any `δ > 0`, `{X − Y ≥ μ} ⊆ {X ≥ μ(1+δ)} ∪ {Y ≤ μδ}`. The one-sample
Chernoff bound for a Beta is *exact* in closed form — minimising
`E[e^{λ(X−t)}] = (1−λ(1−t))^{−α}(1+λt)^{−β}` (Legendre form) over `λ < 1/(1−t)` cancels the
Γ-factors and yields, for `t ≥ μ` and dually for `t ≤ μ`,

  `Pr(X ≥ t) ≤ φ(t) = (t/μ)^α · ((1 − t)/(1 − μ))^β`.

Substituting `t = μ(1+δ)` and `t = μδ` gives `Pr(X ≥ μ(1+δ)) ≤ A(s)^α` and
`Pr(Y ≤ μδ) ≤ B(s)^α` *exactly*. Hence

  `Pr(X − Y ≥ μ) ≤ A(s)^α + B(s)^α`   for every `s ∈ (0,1)`,   (★)

and by the `X ↔ Y` symmetry `Pr(|X − Y| ≥ μ) = 2·Pr(X − Y ≥ μ)`.

There is a second, cleaner form of the same identity in the variable `ε := 1 − s`
(used in the numerics because `s* → 1` in one regime):
`A = (1 + ρ − ρε)ε^ρ` increasing in `ε`, `B = ρ(1 − ε)(1/ρ + ε)^ρ` decreasing in `ε`, so
`min_s max(A,B)` is attained at the *unique crossing* `A(ε*) = B(ε*)`.

#### GAP-2b — the ceiling of (★) is `0.883997`, i.e. `c = 0.123302 < 1/8`

**The two closed forms are exact, not merely bounds.** Solving `∂_λ log E[e^{λ(X−t)}] = 0`
gives the stationary point in closed form, and at it the Γ-factors cancel identically:
for the upper tail, `λ* = (α(1−t) − βt)/(t(1−t)(α+β))` and hence `Pr(X ≥ t) = φ(t)` *exactly*;
for the lower tail at `t = μδ`, `v* = (1−δ)/(δ(1−μδ))` and

  `Pr(Y ≤ μδ) = (1/δ)^{−α}·((1−μ)/(1−μδ))^{−β} = δ^α·((1+ρ−δ)/ρ)^β`,   i.e. `B(s)^α`.

Verified numerically against the analytic stationary point (no optimiser — the earlier apparent
`L(δ)` "disagreements" were scipy failing on a steep `(1−vt)^{−β}`, not algebra): max relative
error **1.5e−14** over 11 `(α,β)` pairs × 8 `δ` values, spanning `α ∈ [0.2,20]`, `β ∈ [1,100]`.

The crude bounds `(1 − t/ρ)^ρ ≤ e^{−t}` and `(1 + (1−t)/ρ)^ρ ≤ e^{1−t}` (both instances of
`(1 + x/n)^n ≤ e^x`, valid for all real `x` and all `n > 0`) give

  `A(s) ≤ (1 + t)e^{−t}`,   `B(s) ≤ t·e^{1−t}`,   `t := ρs ∈ (0, ρ]`.

Minimising `max((1+t)e^{−t}, te^{1−t})` over `t`: the two sides are equal exactly when
`(1+t)/t = e`, i.e. at `t* = 1/(e−1) = 0.581976707`, where both equal `e/(e−1)·e^{−1/(e−1)}
= 0.8839970429`. So

  **`sup_{s,ρ} [A(s)^α + B(s)^α]^{1/α} = e/(e−1)·e^{−1/(e−1)} = 0.8839970429`**,
  **`−log(0.8839970429) = 0.123302`**.

> **[CORRECTED 2026-09-17 — trap P-62.  The displayed supremum is mis-stated and is retained only
> as the superseded record; nothing below asserts a positive bound on `r` or on `α`.]**
> `sup_{s,ρ} [A(s)^α + B(s)^α]^{1/α} ≥ 1`, not
> `0.883997`: the `sup` ranges over `s → 0` (i.e. `δ = ρs → 0`), where `A → 1` and `B → 0`, so
> `[A^α+B^α]^{1/α} → max(A,B) → 1`.  What the crude-bound calculation above establishes — and the
> object the finite-`ρ` convergence in the next paragraph is about — is
> **`sup_ρ min_δ max(A,B) = e/(e−1)·e^{−1/(e−1)} = 0.8839970429`**: a statement about the `ρ → ∞`
> limit of the one-dimensional quantity `min_δ max(A_ρ,B_ρ)`, not an identity for `[A^α+B^α]^{1/α}`
> at fixed `α`.
>
> Two finite-`α` consequences were recorded here, and both are **retracted**:
>
> * `A(δ₁)^α + B(δ)^α ≥ max(A(δ₁),B(δ))^α ≥ m(ρ)^α` with `m(ρ) = inf_δ max(A_δ,B_δ)` (no AM–GM),
>   giving the `ρ`-dependent ceiling `r ≤ sqrt(−log m(ρ)/(11/100))` — `2.1435` at `ρ = 1/2`,
>   `1.6172` at `ρ = 1`, `1.3467` at `ρ = 2`, `1.1773` at `ρ = 5`, `1.0889` at `ρ = 20`, `1.0648` at
>   `ρ = 100`, `1.0587` only as `ρ → ∞` — **[RETRACTED — 该替换使用了对称切片的一维下界,对 `hnum`
>   无效]**.  It used the symmetric slice `δ₁ = δ` (with `B` monotone on `(0,1]`, valid only at
>   `r = 1`), whereas `hnum` binds **two independent parameters** (`δ₁` inside `chernoffA`, `δ`
>   inside `chernoffB`) linked only by `hrel : δ₁ ≤ r−1+δ`.  The one-dimensional infimum over that
>   slice is an **upper** bound of the two-dimensional infimum over the admissible set, not a lower
>   bound; and the two-dimensional infimum **collapses to `0`** whenever `ρ ≲ r−1` (take `δ₁ → ρ⁻`,
>   so `A(δ₁) → 0`, and `δ → 0`, so `B(δ) → 0`).  So `hnum` is satisfiable for arbitrarily large
>   `r`: **this route yields no upper bound on `r` at all.**
> * the reading of `0.8839970429` as a bound valid at finite `ρ` — likewise retracted:
>   `min_δ max(A_ρ,B_ρ)` is `0.750000` at `ρ = 1`, `0.882745` at `ρ = 100`, with limit
>   `0.8839970429`.
>
> `c₀ = 11/100` is **[UNDERIVED — 常数依据待独立重导]**: the threshold
> `α < log 2/(0.123302 − 0.11·r²)` (`≈ 52` at `r = 1`) it was originally read off is downstream of
> the false chain corrected here, and no replacement derivation is claimed.  The `α`-threshold
> `≈ 52` at `r = 1` quoted in `cards/L5.md` and in `lean4/TSDPP/BetaConcentration.lean` is
> **numerically supported but not derived** by this argument; those two sites carry the same
> correction.  This is *not* a claim of a wall at `r ≈ 1.06`.

The supremum is *attained only in the limit `ρ → ∞`* (at finite `ρ` the exact-`A`/exact-`B`
crossing is strictly smaller and increases to the limit: `0.871389` at `ρ=10`, `0.882745` at
`ρ=100`, `0.883872` at `ρ=10³`, `0.8839970` at `ρ=10⁸`, and the `ρ→∞` value `0.8839970429` agrees
with the crude bound to all printed digits — the crude bound is tight exactly in that limit).

> **Register trap P-23 here a second time.** The `ρ = 100` figure `0.882745` was briefly adopted as
> *the* ceiling, displacing the correct `0.883997`, because a finite grid was read as a supremum.
> The two differ in the 3rd decimal and *straddle nothing* here — but the same error in the other
> direction would have straddled `1/8 = 0.125 ↔ e^{−1/8} = 0.882497`, which is the entire question
> of this section. A supremum over a `ρ → ∞` limit is invisible to any finite `ρ`-grid; the closed
> form `e/(e−1)·e^{−1/(e−1)}` is what settles it, and it was already recorded. Therefore:

> **(★) cannot yield `c = 1/8`.** The best constant the union bound gives is `0.123302`, and no
> choice of `s` or refinement of `φ` improves it — `φ` is already the *optimal* member of its
> Chernoff family, and the `ρ → ∞` limit saturates the crude estimate.

The shortfall is `1.4%` (`0.123302` vs `0.125`). Being that close is a trap in itself: it invites
the belief that a small tweak closes it. It does not — see GAP-2c.

#### GAP-2c — what is *not* available (so the gap is not closable by this method)

* **2-D Chernoff on `X − Y` directly** would give the right order (`≈ e^{−α(1+1/ρ)/4}` at `ρ=1`,
  comfortably beyond `e^{−α/8}`), via `1{x ≥ y+μ} ≤ e^{λ(x−y−μ)}` and
  `E[e^{λX}]·E[e^{−λY}]`.
  *[Scope, per P-67: the exponent above is for a deviation of size **`μ`** — the `r = 1` case — and
  must not be read as `αr²(1+1/ρ)/4`. At deviation `rμ` the rate function leaves its quadratic region:
  the true exponent is **sub-quadratic** in `r`, so `c_eff := −log(P/2)/(αr²)` decreases in `r` and
  falls below `1/8` at `r ≳ 9` (numerically at `(12,580)` the per-unit-`r` growth is `10.6, 13.5,
  20.2` at `r = 10, 20, 36`, against a quadratic claim of `13.2, 26.4, 47.5`). The heuristic is sound
  exactly where it was derived, and misleads if extended.]*
  **Rejected**: `E[e^{λX}]` for `X ~ Beta(α,β)` is `₁F₁(α; α+β; λ)` —
  a confluent hypergeometric. Mathlib has no `₁F₁`, and no path to one short of building the
  function. This is the single reason the constant is lost.
* **Exact conditioning** `Pr(X−Y ≥ μ) ≤ ∫_0^{1−μ} φ(y+μ) f_Y(y) dy` (no union bound at all)
  is numerically far better — the effective constant is `≥ 0.2367` across the tested grid, i.e.
  *twice* the paper's `1/8`. **Rejected for formalization**: after the substitution `y = (1−μ)z`
  the bound is
  `(1−μ)^{2β}/(μ^α(1−μ)^β B(α,β)) · ∫_0^1 ((1−μ)z+μ)^α (1−z)^β z^{β−1}(1−(1−μ)z)^{α−1} dz`,
  and pushing it under `e^{−α/8}` needs a lower bound on the Beta function `B(α,β)` uniform in
  `(α,β)` — i.e. a Laplace-method/Stirling estimate. Substantially more hard analysis than the
  union bound, for a constant we have already decided is asymptotically immaterial (GAP-2b).
* **`(u,v)`-reformulation.** With `G_i ~ Γ` and `u = G₂/G₁`, `v = G₄/G₃` independent, the event is
  `(1−μ)v − μ − (1+μ)u − μuv ≥ 0`. A genuine simplification of the *event*, but it does not by
  itself bound the probability; recorded because it is the natural starting point if anyone
  later attacks the `₁F₁` route.
* **Tilt-by-κ, Laplace/second-derivative, crude density comparison, incomplete-gamma/Weierstrass,
  convexity-MGF, integer-moment Markov, Chebyshev/variance.** All rejected earlier; the first three
  reduce to the `₁F₁` obstruction or give only polynomial decay, and Chebyshev is useless for an
  exponential tail. See §5 J-10.

#### GAP-2d — what *will* be formalized

`c₀ = 11/100`, with a **two-case witness** (`t = 29/50 = 0.58`), chosen so every numeric step has
a provable margin:

| case | witness | obligation |
|---|---|---|
| `ρ ≥ 29/50` | `s = (29/50)/ρ` | `(1+t)e^{−t} ≤ e^{−c₀}` (margin 1.26%) and `t·e^{1−t} ≤ e^{−c₀}` (margin 1.48%) |
| `ρ < 29/50` | `s = 1` | `A(1) = 0`; `B(1) = ρ^{1−ρ} ≤ (29/50)^{21/50} = 0.795499 ≤ e^{−c₀}` (margin 11%) |

The two exponential comparisons are discharged without any `₁F₁`, and both verify to *rational*
arithmetic (so `norm_num` closes them) by the two Mathlib primitives
`Real.sum_le_exp_of_nonneg {x} (0 ≤ x) (n) : ∑_{i<n} x^i/i! ≤ exp x` (lower bound, in
`Mathlib/Analysis/Complex/Exponential.lean` §`namespace Real`) and
`Real.exp_bound {x} (|x| ≤ 1) {n} (0 < n) : |exp x − ∑_{m<n} x^m/m!| ≤ |x|^n · n.succ/(n! · n)`
(upper bound, same file):

* `(1 + t) ≤ e^{t−c₀}`: exponent `29/50 − 11/100 = 47/100`. `Real.sum_le_exp_of_nonneg` at
  `x = 47/100`, `n = 4` gives `e^{0.47} ≥ 1.597753`, and `1 + t = 1.58` (margin 1.1%).
* `t ≤ e^{t−1−c₀}`: exponent `29/50 − 1 − 11/100 = −53/100`, so this is `e^{53/100} ≤ 50/29`.
  `Real.exp_bound` at `x = 53/100`, `n = 4` gives `e^{0.53} ≤ 1.695263 + (0.53)^4·5/96 = 1.699371`,
  and `50/29 = 1.724138` (margin 1.4%).

No `norm_num` on `exp`/`log` is needed anywhere: both sides are rationals by the time the
comparison is made.

**Status: closed.**  `TSDPP.unionWitness` in `Scratch/UnionBound.lean` proves the two obligations
above for every `ρ > 0` with the stated witness `s = min 1 (29/(50ρ))`, `sorry`-free, with
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no `native_decide`, no
`unsafe`, no floats).  Both case-2 sub-obligations are met: `A(1) = (1+ρ)·0^ρ = 0` and
`ρ^{1−ρ} ≤ e^{−(21/50)²} ≤ e^{−11/100}` (the cheaper certificate of P-29 rather than the
`(29/50)^{21/50}` one prescribed above).  Verified independently at 60-digit precision: the
witness's global `sup_ρ max(A,B)` is `0.8847…`, attained as `ρ→∞` and consistent with GAP-2b's
`0.883997` ceiling, so `c₀ = 11/100 < 0.123302` is *not* improved by this route — as GAP-2b predicts.
The four comparison certificates evaluate to `1.597754 ≥ 1.58`, `1.699372 ≤ 1.724138`,
`−0.1764 ≤ −0.11`, and `0 ≤ e^{−11/100}`.

**Dependencies for the Lean proof** (all now on the critical path):
`betaMeasure`/`betaPDFReal` (Mathlib), `TSDPP.gammaMeasure_lintegral_exp` (done — this *is* the
`(1−λ)^{−α}` step), the **Beta–Gamma ratio law** `Beta(α,β) = law(Γ_{α,1}/(Γ_{α,1}+Γ_{β,1}))`
(in progress), and the product measure for the independent pair `(X,Y)`.

#### GAP-2e — the two-sample assembly (paper Eq (31)); the `r = 1` core, and why it does *not* cover `r > 1`

The paper's Lemma 5 (Eq (31)) reads, verbatim from p. 9: *"If `X` has a beta distribution
`Beta(α, β)` and `Y` is an independent copy of `X`, then, **for all `0 ≤ r ≤ 1`**, we have
`Pr(|X − Y| ≥ r E(X)) ≤ 2e^{−αr²/8}`."*

Its **use** is Eq (33): `r^l_i = max{1, √(8 log T / α^l_i)}`, i.e. `r^l_i ≥ 1`, and the paper then
writes `Pr(ε_i^c) ≤ 2e^{−α^l_i (r^l_i)²/8}`. So the lemma is *stated* on `r ≤ 1` and *used* at
`r ≥ 1` — the two ranges meet only at `r = 1`.

> **[RETRACTED 2026-09-17 — traps P-62/P-64/P-67.  This paragraph previously argued: "That is not a
> defect to repair: for `r ≥ 1`, `{|X−Y| ≥ rμ} ⊆ {|X−Y| ≥ μ}` and `e^{−cα} ≤ e^{−cαr²}` (as
> `r² ≥ 1`), so **the `r = 1` case implies every `r ≥ 1` case** ... The formalization therefore takes
> `r = 1` as the core and derives `r ≥ 1` from it."]**
>
> The argument is **invalid, and its direction is reversed.** Both displayed facts are true —
> the event shrinks with `r`, and `e^{−cα} ≤ e^{−cαr²}` — but the second one is the *wrong way
> round for the purpose*. The subset relation gives
> `Pr(|X−Y| ≥ rμ) ≤ Pr(|X−Y| ≥ μ) ≤ 2e^{−cα}`, whereas the `r`-case needs
> `2e^{−cαr²}`, which is **smaller** than `2e^{−cα}` for `r > 1`. So the `r = 1` bound does *not*
> imply the `r > 1` bound; it is strictly weaker there. The consequence is not a bookkeeping defect
> that a "start at `r = 1`" convention repairs — the `r > 1` case is a genuinely stronger statement,
> and it is not implied by the stated range. See P-64 (it is false) and P-67 (it is false on the
> paper's own Eq (33) parameter curve, against the paper's own `1/8`).

**The union bound.** With `μ := α/(α+β)`, `ρ := β/α`, `δ := ρs` and the witness `s` of GAP-2d:

  `{|p.1 − p.2| ≥ μ} = {p.1 − p.2 ≥ μ} ∪ {p.2 − p.1 ≥ μ}`, and the two are equimeasurable under
  `Measure.prod_swap` because the two factors are the *same* measure `betaMeasure α β`. So it
  suffices to bound `prod {p.1 − p.2 ≥ μ}` and double. Then

  `{p.1 − p.2 ≥ μ} ⊆ {p.1 ≥ μ(1+δ)} ∪ {p.2 ≤ μδ}`,

since `p.1 < μ(1+δ) ∧ p.2 > μδ ⟹ p.1 − p.2 < μ(1+δ) − μδ = μ`.

**The two Chernoff parameters are forced, and they are exactly the stationary points.** To make
the one-sample output `(1 − u(1−t))^{−α}(1 + ut)^{−β}` equal `A(s)^α = (1+ρs)^α (1−s)^β` — using
`β = ρα` — one must have `1 − u(1−t) = 1/(1+ρs)` and `1 + ut = 1/(1−s)`. Solving gives

  `t = t₁ := μ(1+δ) = (1+ρs)/(1+ρ)`,  `u := s(1+ρ) / ((1+ρs)(1−s))`,

and then `u(1−t₁) = ρs/(1+ρs) < 1` ✓, `ut₁ = s/(1−s)` ✓. So the substitution is *determined* by the
requirement that the elementary Gamma Laplace transform reproduce the Beta Chernoff exponent —
which is the whole reason no `₁F₁` is needed (GAP-2c). Symmetrically the lower tail at
`t₂ := μδ = ρs/(1+ρ)` takes

  `v := (1 − ρs)(1+ρ) / ((1+ρ−ρs)·ρs)`,   needing `ρs < 1`,

and gives `(1 + v(1−t₂))^{−α}(1 − vt₂)^{−β} = (ρs)^α (1/ρ + 1 − s)^β = B(s)^α` ✓.

**`ρs < 1` is exactly what forces the case split of GAP-2d.** In the branch `ρ ≥ 29/50` the witness
is `s = 29/(50ρ)`, so `ρs = 29/50 < 1` ✓ and `s < 1` ✓ — both `u` and `v` finite and positive. In
the branch `ρ < 29/50` the witness is `s = 1`, where `s/(1−s)` is undefined, so that branch is
**not** handled by the `u`/`v` substitution at all: it uses `t₁ = μ(1+ρ) = 1`, whence
`Pr(X ≥ 1) = 0` outright (the Beta measure gives no mass to `Ici 1`), and the lower tail reduces to
the already-proved `B(1)^α = ρ^{(1−ρ)α} ≤ e^{−(21/50)²α} ≤ e^{−c₀α}` from GAP-2d.

**Conclusion formalized.** For `0 < α`, `0 < β` and `r ≥ 1`,

  `Pr_{Beta(α,β)⊗Beta(α,β)}( |X − Y| ≥ r·α/(α+β) ) ≤ 2·e^{−(11/100)·α·r²}`,

with the explicit constant `11/100` in place of the paper's `1/8` (GAP-2b: the paper's constant is
unreachable by this method; `11/100 = 0.11 < 0.125 = 1/8`, so the bound is strictly weaker but has
the same form, the same quantifier order, and the same hypothesis set — including the paper's own
`μ = α/(α+β)` and its own `r ≥ 1` use).

### GAP-3 — `C` and `D` are not T-free constants
The paper (§IV) asserts "we consider the state space of `X_i(t)` to be finite, i.e. `X_i(t) ≤ D`" and
"the time intervals for selecting the same arm are finite, i.e. `δ_i ≤ C`", then uses `(C+D)` as a
*deterministic* bound on `Y_i(t)` inside the prefactor `(½C² + (2C²+2CD+C)L)` of Eq (38).
But the only source for the state bound is Lemma 6, which is a **high-probability** statement with
`D = ⌈log ε / log(1−θ_i)⌉`. Three consequences the paper does not address:
1. `D` depends on the confidence `ε`, hence on `T`; to make `D` T-free one needs `θ_i ≤ 1−c` bounded away
   from `1`. The paper does state the simulation uses `θ_i ~ Beta(1,1)`, which is *not* bounded away
   from 1.
2. The bound `Y ≤ C+D` therefore holds only with probability `1−ε`, so it cannot be pulled out of the
   expectation in Eq (38) as a constant factor without an extra tail term. Eq (38) does not carry one.
3. `C` (max re-selection interval for a fixed arm) is *itself* what the policy controls; under the
   belief-DPP argmin there is no argument in the paper bounding it a priori.
This gap is *repairable* — add a `1−ε` term and pay `O(ε·L·maxY)` — but as written the prefactor is not
justified. Recorded rather than silently patched.

### GAP-4 — the exponent in Eq (19)
`O(√(L³T log T))` (Theorem 2, §IV) vs `O(√(T log T))` (abstract, §I-C, §VII conclusion). These agree
only if `L` is treated as a constant independent of `T`; the paper never says which.
Carrying the paper's own arithmetic through with `L` symbolic gives
`BR(T) ≤ Θ(L) · 2√(8T(C+D) log T)` (from Eq (39) with `m = T/L`, `η = L/(C+D)`), i.e. **`O(L√(T log T))`**,
which is *stronger* than the claimed `O(L^{3/2}√(T log T))`. So Theorem 2 is not falsified — it is
implied — but the stated exponent `L³` is not what the derivation yields, and neither is the abstract's
`L⁰`. See §8 for the numeric trace.
Consequence for this artifact: we machine-check the **assembly step** (R14) as an exact finite-sum
statement with the exponent left symbolic, so the artifact is agnostic between the three readings and
records which one the paper's own computation supports.

### GAP-5 — the index convention in Eq (9) is inconsistent with Eq (4)
Eq (4) defines `Y_i(t) = X_i(t−1) + 1` when `π_i(t) = 1`; Eq (9) writes the same quantity with
`X_{A_t}(t)`, i.e. one slot later.  The two cannot both be right for a *deterministic* `X`, and
the difference is exactly `1` in the slot where the event fires.
**Resolution taken**: pin Eq (4)'s convention (`TSDPP.penalty_identity` takes the *pre-slot* AoI),
because Eq (4) is the recursion that is actually defined, and note that Eq (35) is invariant under
the choice — both sides of the subtraction use the same index — so `TSDPP.penalty_diff` is
unaffected either way.  The gap is bookkept rather than silently resolved because it *would* matter
for any statement that compares `X_i(t)` and `Y_i(t)` at the same slot, which Eq (36) does.
**Consequence for Eq (36)**: none, because Eq (36) is derived from Eq (35) (the difference of the
two expectations), where the index cancels.  Verified by re-deriving.

### GAP-6 — Eq (40)'s printed final step is *false*
Eq (40) is printed as a three-line chain.  Verified at 600 dpi, cross-checked against the PDF's
own character stream (`... ≤1−16 η e−η/8 1 T + 2m T .`):

  `Σ_{l=1}^{m} Σ_{t=1}^{L} 2e^{−α^l_{A_t}(r^l_{A_t})²/8} ≤ Σ_{l=1}^{n} Σ_{t=1}^{L} 2e^{−α^l_{A_t}/8} + 2m/T`
  `≤ Σ_{l=1}^{n} L·2e^{−ηl/8} + 2m/T ≤ 1 − (16/η)e^{−η/8}·(1/T) + 2m/T`.

There are **no parentheses** around `1 − (16/η)e^{−η/8}`: the `1` is a bare additive constant and
only `(16/η)e^{−η/8}` carries the `1/T`.  An earlier revision of this file quoted the last step as
`(1 − (16/η)e^{−η/8})·(1/T)`; that is a *reconstruction*, not the printed text, and is corrected
here.

Four problems, in increasing severity:
1. **The last step is false, not merely unreconstructible.**  Its left-hand side,
   `Σ_{l=1}^{n} L·2e^{−ηl/8}`, is *independent of `T`* — the truncation index `n` grows, but the
   series converges — and tends to `L·2e^{−η/8}/(1−e^{−η/8})`, a constant increasing in `L`.  Its
   right-hand side tends to `1`.  At the paper's own experimental setting (`L = 20`, `η = 2`) the
   left side is `140.83`, the right side `1.0062` at `T = 10³` and `→ 1`.  So the printed
   inequality asserts `140.83 ≤ 1`.  Falsified numerically in one line by
   `scripts/numeric_check.py`.
   **How far off it is.**  The excess is a *constant factor*, not a growth in `T`.  With
   `n = ⌈8 log T/η⌉` the truncation is nearly invisible (`e^{−nη/8} ≤ 1/T`), so the left side is
   `≥ (16L/η)·e^{−η/8}·(1 − 1/T)`; Corollary 1's `η = ⌊L/(C+D)⌋` (verified verbatim on p9) gives
   `L/η ≥ C+D`, hence `≥ 16(C+D)·e^{−η/8}·(1 − 1/T)` — independent of both `T` and `L`.  The
   printed step therefore asserts roughly `16(C+D) ≤ 1`.  This is exactly why the *conclusion*
   survives: a constant-factor excess in the tail is still `O(1)` in `T`, and after multiplication
   by `K = Θ(LC(C+D))` it is `16LC(C+D)²`, against a main term of `Θ(√(T log T)·(C+D))` — the
   ratio `16LC(C+D)^{3/2}/√(T log T)` tends to `0`.
2. **The first term.**  `Σ_{l≥1} 2e^{−ηl/8} = 2e^{−η/8}/(1−e^{−η/8})`, and `1 − e^{−x} ≥ x·e^{−x}`
   gives the clean bound `≤ 16L/η`.  That — **not** `(16/η)e^{−η/8}/T` — is what the derivation
   supports.  The printed `16/η` is the correct constant; the lost `L` and the spurious `1/T` are
   where it goes wrong.
3. **The `β`/`T` bookkeeping.**  `T = mL` is used inconsistently: some places divide by `T`,
   others by `m`.
4. **The `n` is printed, and it is correct** (correcting an earlier revision of this file, which
   claimed the PDF had no `n` and that `paper.txt`'s `n` was an extraction artefact).  The `n` is
   plainly visible in the 600 dpi render of the second and third lines of Eq (40).  It is the
   truncation index `n = ⌈8 log T/η⌉` introduced in the sentence *above* the display: the `m`
   episodes are split into the first `n` (where `r^l_i` can reach `1`) and the remaining `m − n`,
   whose contribution is the `2m/T`.  So `paper.txt` was right and this file was wrong.

**Resolution taken**: `TSDPP/Tail.lean` proves the *true* bound
(`geom_exp_sum_le`: `Σ_{l<N} e^{−cη(l+1)} ≤ r/(1−r)` with `r = e^{−cη}` — the exponent constant is
the **parameter** `c > 0`, not the paper's literal `1/8`, so that the paper's `c = 1/8` and the
artifact's `c₀ = 11/100` are both instances of one statement; `tail_sum_le`: the `L`-round sum is
at most `L·2r/(1−r) ≤ 2L/(cη)`), **not** the printed expression.  That tail is `O(1)` in `T`, and it
is multiplied by the `O(L)` coefficient `K = ½C² + (2C²+2CD+C)L`, giving an extra term `K·2L/(cη)`.
This is dominated by the first term `K·2L√(K₀m log T/η)` as soon as `1/(cη) ≤ √(K₀m log T/η)`,
which (using `K₀ = 1/c`) is equivalent to `K₀ ≤ m·log T·η` — at the paper's `c = 1/8`, `K₀ = 8` this
is exactly the condition `8 ≤ m·log T·η` below, so the parameterisation reproduces the paper's
threshold rather than moving it.  Either way it holds for all large `T`.  Note the condition is on
the product `c·m·log T·η`, so it is **insensitive to which `c` is used**: `K₀ = 1/c` grows as `c`
shrinks, but so does the admitted radius, and the two movements cancel exactly.  **Theorem 2's conclusion therefore survives**: its rate
and exponent are unaffected.  But the intermediate step is a defect in the paper's *proof* — a
false assertion, not a difference of convention — so `theorem2_withTail` deliberately keeps the
tail as an abstract `B` with `0 ≤ B ≤ √log T` rather than committing to either expression.

## 8. Numeric falsification log (`scripts/numeric_check.py`)

Run before any Lean was written, to (a) find a wrong lemma early and (b) fix constants.
Results (all with 20 000–30 000 random trials):

| target | check | result |
|--------|-------|--------|
| Eq (16) | `Σ x·P_x` vs closed form | max abs diff `1.8e−13` ✓ |
| Eq (15) | `Σ P_x = 1` | max abs diff `1.4e−15` ✓ |
| Eq (21) | indicator form vs case form of the likelihood | max abs diff `0` (exact) ✓ |
| Lemma 2 Eq (23) | `LHS / (2δ·|Δθ|)` | max `1.0000000000000113` — **tight** (trap P-4) |
| Lemma 2 Eq (24) | `LHS / ((δ(δ−1)/2 + δ(λ+δ))·|Δθ|)` | max `1.0000000000000226` — **tight** |
| Eq (25) | `sup_{[0,1]} |f'|` for `f(θ)=θ(1−θ)^x`, `x=0..59` | `1.0` — claim `≤1` ✓ (trap P-3) |
| Eq (39) | `max_m (Σ_{l<m} 1/√(l+1))/(2√m)` | `0.988516` — the `2√m` is sharp up to `1.2%` ✓ |
| Eq (38) constant | symbolic expansion of `½C² + (2C²+2CD+C)L` | `= (½C² + LC) + 2C(C+D)L` **exactly** (see below) |
| GAP-4 | exponent trace `Θ(L)·2√(8T(C+D)log T)` | confirms `O(L√(T log T))` |
| **Lemma 5** | `Pr(X−Y ≥ μ)` by 2-D quadrature vs `e^{−α/8}` | worst ratio `0.234` (at `α=0.5, β=2`); **statement is true**, huge margin |
| **Lemma 5** | union-bound ceiling `min_s max(A,B)` | `0.8839970429` ⟹ `c = 0.123302 < 0.125` — **cannot reach `1/8`** (GAP-2b) |
| **Lemma 5** | witness `t = 29/50`, `c₀ = 11/100`, both branches | `0.884639`, `0.882738`, `0.795499` ≤ `e^{−0.11} = 0.895834` ✓ |

### The `B(s)` transcription bug (cost: one session)

The union-bound ceiling was computed twice and the two runs disagreed (`0.1233` vs `0.2252`). The
**first** run was right. The second passed

```
B(r,s) = (r*s)*(1+(1-s)/r)**r        # WRONG
```

instead of the derived `B(s) = ρs(1/ρ + 1 − s)^ρ`. The two agree only at `ρ = 1`, which is exactly
where they were spot-checked — so the error survived review. Consequence: a wrong ceiling
`0.798341` was reported and the *correct* conclusion that the union bound **fails** to reach `1/8`
was briefly retracted.

Two lessons, both now traps (P-22, P-23 in §6):

* **Check a parametrised identity at a value where the two candidate forms differ.** `ρ = 1` is
  the unique fixed point of this bug; `ρ = 1.4` would have exposed it immediately.
* **The failing regime is `ρ → ∞`, and no finite grid shows it.** `sup_ρ m(ρ)` is a *limit*, not an
  attained maximum — a grid over `ρ ≤ 100` reads `0.882745 < 0.882497`, i.e. "holds". The
  conclusion `c < 1/8` is only visible from the closed-form crude bound
  `max((1+t)e^{−t}, te^{1−t})` with `t = ρs`, where `ρ` drops out entirely. Any numerical
  verification of this claim **must** be done on the `t`-parametrisation, not on a `ρ`-grid.

Both forms of the identity are exact and were re-verified symbolically:
`B(1−u) = A(u)·(ρ(1−u))^{1−ρ}·(1+ρu)^{ρ−1}`.

The Eq (38) row is the decisive one and is reproduced here so it need not be rediscovered.  The
paper's coefficient is `½C² + (2C² + 2CD + C)L`, the per-round coefficient claimed by Eq (36) plus
Eq (37) is `(½C² + LC) + 2C(C+D)L`, and

```
Eq(38) K  = 2*C**2*L + C**2/2 + 2*C*D*L + C*L
mine      = 2*C**2*L + C**2/2 + 2*C*D*L + C*L
difference= 0
```

**This is what forced `LC` rather than `C(C+D)` in Eq (36).**  The `C(C+D)` route (also derivable
from Lemma 6) leaves `2C²L` unmatched, so Eq (38) would not follow; see route J-9 in §5 and
`TSDPP.meanCoeff_le`.

The two "tight" rows are the reason `cards/R9.md` does **not** attempt to sharpen either constant.

## 9. Collaboration protocol (per `CLAUDE.md` §协作方式)

* **Seed prompts.**  When a strictly simpler sub-problem closes, its Lean name is handed to the
  group attacking the harder problem; the harder group may not re-derive it.  Actual hand-offs made:
  * `Belief.pmf_mean` (R6) → the R9 group (the first-moment bound needs the same weighted
    geometric sum).
  * `Lipschitz.l1_lipschitz` / `firstMoment_lipschitz` (R9) → the R10 group.  `Regret.beliefMean_diff_le`
    is literally `firstMoment_lipschitz` plus `abs_sum_le_sum_abs`; the R10 group did not re-prove
    Lemma 2.
  * `Assembly.sum_range_inv_sqrt_le` (R14) → the R16 group, which consumes it as the Eq (39) input.
  * `StateBound.tail_le_eps` (R12a) → the R10 group, which consumes `δ ≤ C` as a hypothesis.
* **Cross-pollination.**  The coordinator does not write the subagents' tactics; it aggregates
  intermediate results and redistributes them.  Traps P-1…P-17 in §6 are exactly such
  redistributions — each was found in one workstream and is on the critical path of another.
  Two were found *independently twice* (P-15, P-17), which is why they carry an explicit note.
* **Human judgement at the top only.**  No human tactic-writing was requested or used.  The only
  human inputs were the high-level priorities: "formalize the paper", and the constraint that
  cited results must be hypotheses rather than axioms.
* **State-layer rebuild.**  Trigger: an agent stops citing closed cards and starts re-proving them,
  or the status board in §3 and the actual `#print axioms` audit disagree.  **This triggered once,
  at the end of the first work session**: the §3 board named declarations
  (`TSDPP.Assembly.regret_assembly`, `TSDPP.Model.chainSucc`, `TSDPP.Round.round_diff_identity`,
  `TSDPP.Lipschitz.belief_l1_le`, `TSDPP.Conjugacy.posterior_eq_betaMeasure`,
  `TSDPP.StateBound.chain_tail`) that had never existed, and listed R7/R9/R12a/R15/R14 as CLOSED
  when only R5/R6 had been built.  Response taken: stop, regenerate §3 from `lake build` output and
  from `grep -nE "^(theorem|lemma|def)" TSDPP/*.lean`, then resume.  The board is now mechanically
  checkable against the source tree.

## 10. Reproducing the artifact

One command does the whole verification:

```
cd lean4
./scripts/check_axioms.sh
```

It (a) builds the root module, (b) elaborates `TSDPP/Audit.lean` and rejects any elaboration error,
(c) accounts for **every** `#print axioms` line by name — a declaration Lean reports nothing about
has an *empty* axiom set, which passes, while a verdict for a name not in `Audit.lean` fails —
and rejects any declaration depending on an axiom outside `{propext, Classical.choice, Quot.sound}`,
and (d) scans every source file for `sorry`/`admit`/`native_decide`/`unsafe` **outside comments**
(block comments in Lean nest, so the scan uses `scripts/scan_forbidden.py` rather than a regex).
Last run:

```
     43 audited, 40 reported, 3 with an EMPTY axiom set: copyStep, copyStep_other, copyStep_self
OK: 13 source files scanned, no sorry, admit, native_decide, unsafe in code
OK: 43 declarations audited; each depends on nothing, or on a subset of
    {propext, Classical.choice, Quot.sound}
```

Two cautions about this gate, both learned the hard way (traps P-20, P-21):

* It was twice **wrong in the direction of false rejection**, and both times the fix was to accept
  a *stronger* result rather than to weaken the check.  First `copyStep_iterate` was rejected for
  depending on `[propext, Quot.sound]` — a strict subset of the allowed three — so the check became
  set *membership* rather than string equality.  Then the count `declared == reported` rejected the
  three `rfl`-proved declarations Lean prints nothing about, because an empty axiom set is stronger
  still; the check is now name-level.  A gate that fails on stronger evidence is a gate that will
  eventually be "fixed" by weakening it.
* The gate is only as good as its negative control, and the negative control must not be a
  mutate-then-restore in a command that can be killed.  Trap P-20: a `sed -i` mutation of
  `Assembly.lean` was interrupted by a tool timeout *between* the mutation and the restore, leaving
  a truncated file on disk.  Prefer standalone unit tests of the check's logic (feeding it synthetic
  input) to mutating the real artifact; when mutation is unavoidable, write the restore into a
  `trap`/`finally`, not into the next command.

The individual steps, if you want them separately:

```
export PATH="$HOME/.elan/bin:$PATH"
lake build                                    # whole development
lake env lean TSDPP/Audit.lean                # the raw #print axioms report
python scripts/scan_forbidden.py              # the comment-aware source scan
python ../scripts/numeric_check.py            # the falsifiers of §8
```

`TSDPP.lean` imports every module, so `lake build` compiles the whole development (trap P-15).
`Audit.lean` is deliberately *not* imported by it — `#print axioms` is a command, not a
declaration, and importing it would put audit output in every build.

**Two operational cautions**, both from real incidents (traps P-15, P-20):
* `lake env lean <file>` does not build that file's dependencies — a freshly added lemma reads as
  `unknownIdentifier` until you `lake build TSDPP.<Dep>`.  `check_axioms.sh` builds first for this
  reason.
* Do not run a *mutate-then-restore* test (e.g. injecting a `sorry` to prove the gate fires) inside
  a single shell invocation that a timeout can kill: the kill can land between the two, leaving a
  real source file broken.  Use a scratch copy outside the repo.

## 11. `TSDPP/BetaGamma.lean` — law of the Gamma ratio (closed)

Statement (public theorem, one declaration; every helper is `private` so the module can be
imported alongside `BetaMeasureIci.lean` / `OfRealAlgebra.lean` / `GammaExpIntegral.lean` /
`SubstLemmas.lean`, which declare the same helper names non-privately):

```lean
theorem gammaMeasure_prod_ratio {a b t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ht0 : 0 < t) (ht1 : t < 1) :
    (gammaMeasure a 1).prod (gammaMeasure b 1) {p : ℝ × ℝ | t * p.2 ≤ (1 - t) * p.1}
      = betaMeasure a b (Ici t)
```

`#print axioms TSDPP.gammaMeasure_prod_ratio` →
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

**Deviation from the spec header, deliberate and minimal:** one line, `open Set`, had to be added
so that the spec's bare `Ici t` resolves (`Ici` is `Set.Ici`; without the `open` it is an
`unknownIdentifier`).  Nothing else in the requested header/signature was changed.

### 11.1 Route (why only affine substitutions were needed)

Naive route: substitute `u = x + y`, `r = y/(x+y)` — that is a Möbius map and needs a Jacobian
computation in `ℝ × ℝ` (route REJ-11.1 below).  Closed route instead:

1. `gammaMeasure a 1 = volume.withDensity (gammaPDF a 1)` definitionally, so the product is
   `(volume.withDensity f).prod (volume.withDensity g) = (volume.prod volume).withDensity F`
   with `F p = f p.1 * g p.2`.  The goal becomes
   `∫⁻ p, A.indicator F p = betaMeasure a b (Ici t)`.
2. Translation `u = p.1 + p.2` only (`lintegral_sub_right`, `map_add_right_eq_self`): for each
   fixed `u` the inner integral is over the whole `y`-line, and the indicator condition
   `t*y ≤ (1-t)*(u-y)` is *linear* in `y`.
3. Substituting `y = u * r` (`lintegral_mul_left_of_pos` with `u > 0`,
   `Real.map_volume_mul_left`) makes the condition `t*r ≤ (1-t)*(1-r)`, i.e. `r ≤ 1-t`, and pulls
   `ENNReal.ofReal u` out of the inner integral.  This is the step that avoids the Möbius map:
   *scaling by a positive constant*, not a ratio, because the ratio was already resolved by the
   translation.
4. Reflection `r ↦ 1-r` on the remaining Gaussian-type integral (`setLIntegral_one_sub`,
   `setLIntegral_one_sub'`) turning `(1-r)^(a-1) r^(b-1)` on `Ioc 0 (1-t)` into
   `w^(a-1) (1-w)^(b-1)` on `Ico t 1`, then `setLIntegral_congr_of_diff_subset_singleton` to
   move `Ico t 1` to `Icc t 1` (the single point `1` has measure zero — `Real.volume_singleton`).
5. The `u`-integral collapses with `Real.integral_rpow_mul_exp_neg_mul_Ioi`:
   `∫_0^∞ u^(a+b-1) e^(-u) du = Γ(a+b)`, together with `Real.rpow_add`, `Real.mul_rpow`,
   `Real.exp_add`.
6. Collect constants (`setLIntegral_congr_fun` + `← ENNReal.ofReal_mul` + `ring`) and identify the
   result with `betaMeasure a b (Ici t)`, whose closed form is proved inline as the private lemma
   `betaMeasure_Ici` **before** the main theorem (declaration order matters).

### 11.2 Rejected routes

* **REJ-11.1 — polar / Möbius substitution `(u,r) ↦ (ur, u(1-r))`.**  Correct mathematically but
  requires a Jacobian in `ℝ × ℝ` and a `Measure.map` of a genuinely nonlinear (rational) map.  All
  the needed machinery for the affine case (`map_add_right_eq_self`, `Real.map_volume_mul_left`)
  exists in Mathlib; the corresponding "map under a rational map" does not.  Rejected after the
  translation step (11.1.2) showed the ratio could be produced by *linear* substitutions only.
* **REJ-11.2 — `lintegral_map` + `Measure.map` of the ratio directly** (the coordinator's
  `Measure.map (fun p => p.1/(p.1+p.2)) ... = betaMeasure a b` framing).  Not weaker, but strictly
  *more* work: `Measure.ext_of_Ici` then requires the same CDF computation for every `t`, plus it
  needs `Ici`-continuity/`MeasurableSingletonClass` bookkeeping at `t = 0, 1` that the direct CDF
  statement with `0 < t < 1` skips.  The delivered CDF identity *implies* the map identity via
  `Measure.ext_of_Ici`, so the stronger-and-cheaper statement was kept.
* **REJ-11.3 — `ProbabilityTheory.beta` / `betaPDF` closed-form manipulation via `Real.beta`.**
  `Real.beta a b = Γa Γb / Γ(a+b)` exists, but pushing the goal through `Real.beta` fought
  `ENNReal.ofReal` nonnegativity side-goals at every `rw`.  Inlining the `Ici`-form of
  `betaMeasure` as a private lemma and doing the `ofReal` algebra once at the end was cheaper.
* **REJ-11.4 — `rw` chains instead of `exact`/`congrArg`.**  See trap T-11.9.

### 11.3 Lean traps met here (logged as encountered, per `CLAUDE.md`)

* **T-11.1 — `rw [lem h]` fails on `hr : 0 < r` against a lemma whose statement is `Ioi 0`.**
  The lemma's set metavariable unifies with the beta-reduced `Real.lt 0`, which is not
  syntactically `Ioi 0`; the error prints the pattern as `indicator (Real.lt✝ 0) ?f r`.
  Fix: never feed `hr`; feed the membership explicitly —
  `rw [Set.indicator_of_mem (show r ∈ Ioi (0:ℝ) from hr)]` (and `..._of_notMem` with `∉`).
* **T-11.2 — `rw` cannot rewrite under a binder when the instance would capture the bound
  variable.**  `rw [ite_eq_left hu]` on `∫⁻ r, (if 0 < u then K r else 0)` fails because the
  rewrite happens under `∫⁻ r,`.  Fixes, in order of preference:
  `simp only [ite_eq_left hu]`; `exact`; or lift the equation to top level with
  `lintegral_congr` / `setLIntegral_congr_fun` and then `rw`.
* **T-11.3 — tactic-mode `rw [a, b]` is not `rw [a]; rw [b]`.**  A combined `rw` normalises the
  goal after the first rewrite and can make the second pattern disappear.  Splitting into separate
  `rw` tactics (and re-`show`ing the goal between them) fixed several occurrences.
* **T-11.4 — bracket bookkeeping for `rw [show ... from by ...]`.**  The `]` closing the outer
  `rw [` must come *after* the last inner tactic of the `by` block; a naive line splice drops it.
* **T-11.5 — `Set.mem_diff` is deprecated.**  Use `Set.mem_sdiff`; and where the goal is an
  `Or`/`False`, `.elim` on the resulting proof term (`(hx.2 ⟨…⟩).elim`) avoids a `simp` that
  would trip the deprecation warning.  Warnings are fatal here (zero-warning requirement).
* **T-11.6 — `measurableSet_singleton` is not applicable bare.**  `lintegral_indicator
  measurableSet_singleton` fails; write `measurableSet_singleton 0`.
* **T-11.7 — `by positivity` fails when the goal is a metavariable**, e.g. inside
  `rw [← ENNReal.ofReal_mul (by positivity)]` the nonnegativity side-goal is not yet known.
  Fix: state `hC : 0 ≤ <expr>` (and `hB`, …) as real hypotheses and pass them by name.
* **T-11.8 — wrong occurrence selected by `rw [← hlin]`.**  In the `h5c` step the backward
  rewrite matched an inner occurrence and left the goal unsolved (and with only `rw [← hlin]` plus
  `exact congrArg …` Lean reported "No goals to be solved").  Robust form:
  `exact congrArg (fun x => ENNReal.ofReal u * x) (hlin.symm.trans (hKfull u))` — build the
  equation by `trans` and apply it with `congrArg`, never by search-and-replace.
* **T-11.9 — `lintegral_zero` type mismatch.**  Goal RHS was `0 * ofReal (Γ(a+b))`, not `0`.
  Fix: `exact lintegral_zero.trans (zero_mul _).symm`.
* **T-11.10 — declaration order.**  A private lemma used inside the main proof must be *declared
  before* it; Lean has no forward references at tactic level.  `betaMeasure_Ici` moved up.
* **T-11.11 — the `Edit` tool reported "String to replace not found" on multi-line blocks that
  looked byte-identical** (likely whitespace/CRLF normalisation after the earlier splice).  Fix:
  line-index splicing with Python (`io.open(..., encoding='utf-8')`), which is reproducible.
* **T-11.12 — probe files must not live under `TSDPP/`.**  `scripts/scan_forbidden.py` exits 1 on
  any file under `TSDPP/` whose stem starts with `probe`/`scratch`/`test`/`tmp`.  All probes went
  to `lean4/Scratch/` (`PT.lean`, `PT2.lean`, `Scratch5.lean`), outside the scan root.

### 11.4 Unresolved gaps (this module)

* **GAP-11.1 — no gap in the closed statement.**  The theorem is proved for all `0 < a`, `0 < b`,
  `0 < t`, `t < 1`, with no extra hypotheses and no axioms beyond the three standard ones.
* **GAP-11.2 — the endpoint cases `t = 0` and `t = 1` are not covered by this declaration.**
  `Pr(t ≤ X)` for `t ≤ 0` is `1` and for `t ≥ 1` is `0`; these are not formalised here.  If the
  downstream `Measure.map` identity is wanted, `Measure.ext_of_Ici` needs them (or `Ioi`-form
  reasoning instead).  Recorded as a known boundary, not a hidden assumption.

  > **Closed 2026-09-17 by `TSDPP/GammaRatioMap.lean` (task #9).**  `t ≤ 0` and `t ≥ 1` *are* now
  > formalised, in exactly the form this gap prescribed: `Measure.ext_of_Ici` at all `t`, with the
  > two endpoints as separate branches (`0 < t < 1` reuses `gammaMeasure_prod_ratio`; `t ≤ 0` gives
  > value `1`; `t ≥ 1` gives value `0`, and `betaMeasure a b (Ici 1) = 0` is proved once and reused).
  > The statement of GAP-11.2 is therefore historical; the map-level law
  > `betaMeasure α β = ((gammaMeasure α 1).prod (gammaMeasure β 1)).map (fun p => p.1/(p.1+p.2))`
  > is unconditional for `0 < α`, `0 < β`.  See the `gammaMeasure_prod_ratio` row of the DAG and
  > traps P-42…P-47.
* **GAP-11.3 — the "faithfulness" argument (spec item 3) is by hand, not machine-checked.**  The
  Lean statement is the CDF identity that defines `Beta(a,b)`; there is no second, independent
  formalisation of "the ratio of two Gammas" in this repo to prove equivalence against (that would
  be circular).  Written out in §11.1 step by step; a human must judge the transcription.
