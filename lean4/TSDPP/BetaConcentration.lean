/-
Copyright (c) 2026 TSDPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Concentration of the difference of two independent Beta variables (Lemma 5 / Eq (31))

Target as registered (NOT merely unreached — **REFUTED**, see trap P-64 below):

  `Pr(|X - Y| ≥ r·α/(α+β)) ≤ 2·exp(-(11/100)·α·r²)`   for `X, Y` iid `betaMeasure α β`, `r ≥ 1`.

## [2026-09-17 — trap P-64: this target is FALSE, and the range is the reason]

The paper's Lemma 5 (p. 9, verbatim) reads

> If `X` has a beta distribution `Beta(α, β)` and `Y` is an independent copy of `X`, then, **for all
> `0 ≤ r ≤ 1`**, we have `Pr(|X − Y| ≥ rE(X)) ≤ 2e^{−αr²/8}`.

so the artifact and the paper differ in **two** ways: the constant (`11/100` vs `1/8`) *and the range*
(`r ≥ 1` vs `0 ≤ r ≤ 1`).  The artifact did not mistranscribe the constant — it **inverted the
range**, and on the inverted range the bound is false.  Exact rational arithmetic (each row
independently reproduced at 40 dps through the regularized incomplete beta):

| `(α, β, r)` | `Pr(\|X−Y\| ≥ rα/(α+β))`, exact | vs `11/100` | vs the paper's `1/8` |
|---|---|---|---|
| (1, 100, 10) | 2.809651246898e−05 | holds | **fails 3.77×** |
| (2, 200, 10) | 8.606640056681e−09 | **fails 15.43×** | fails 311× |
| (5, 500, 10) | 3.658586854855e−19 | **fails 1.4e5×** | fails 2.6e8× |

"fails `N`×" is the plain ratio `LHS / (2·exp(−c·α·r²))`, with `c_eff := −log(LHS/2)/(αr²)` the largest
constant the row admits.  The two ways of computing it agree identically, since
`LHS / 2e^{−cαr²} = e^{(c − c_eff)αr²}`: at `(2,200,10)`, `8.6066e−09 / 5.579e−10 = 15.43` and
`e^{(0.11 − 0.096319)·200} = 15.43`.

`betaMeasure_prod_abs_sub_le_unionTail` itself remains a **valid implication** — its `r ≥ 1`
hypothesis is inert (`_hr`), and `hnum ⟹ the claimed bound` is correct.  What is refuted is the
*antecedent* being satisfiable there: at `(2,200,10)` the infimum of `A(ρ,δ₁)^α + B(ρ,δ)^α` over the
admissible set is `6.431e−7` (attained at `δ₁ = r−1 = 9`, `δ → 0`) against the required `2.789e−10`
— a **2305× miss**.  The optimal split is pinned by `δ₁ ≤ r−1+δ`, so small tails *force* `r ≥ 1`:
**`1 ≤ r` is exactly the price of this method, and exactly where the claim is false.**

The paper's stated range is where the lemma holds — a sweep of `α ∈ [0.5, 200]`, `ρ ∈ [0.1, 1000]`,
`r ∈ [0.1, 1]` gives `min c_eff = 0.242848`, clearing `1/8` by +0.118 — but it is **not reachable from
this file's toolkit** (see the route analysis at the end of this header).  The paper's own Eq (33)
applies the lemma at `r = max{1, √(8 log T/α)} ≥ 1`, so this is an inherited defect of the source,
not a local slip.  Full record: `DESIGN.md` P-64, `FIDELITY.md` §3.4, `cards/L5.md`.

## [2026-09-17 — trap P-67: the witnesses above are not the worst case, and the paper's own `1/8` fails too]

The rows in the table above sit at `r = 10`, `ρ = 100` — outside the vacuous region, but **off the
curve Eq (33) actually prescribes**.  Walking that curve, `r = max{1, √(8 log T/α)}`, changes the
picture qualitatively.  Independently re-derived (a quadrature that first reproduces the three exact
rows above to 11 significant digits):

| `α` | `ρ` | `T` | `r` | `c_eff` | vs `11/100` | vs the paper's `1/8` |
|---|---|---|---|---|---|---|
| 1 | 50 | `10⁶` | 10.513 | 0.11182 | holds | **FAILS** |
| 1 | 100 | `10⁶` | 10.513 | 0.10623 | **FAILS** | **FAILS** |
| 1 | 50 | `10⁹` | 12.876 | 0.09289 | **FAILS** | **FAILS** |
| 2 | 50 | `10⁹` | 9.105 | 0.11021 | holds | **FAILS** |
| 5 | 100 | `10⁹` | 5.758 | 0.13425 | holds | holds |

The mechanism: `r` grows like `√(log T/α)` while `c_eff` falls in `r`, and does so **sub-quadratically**
— past the CLT region the log-density is near-linear in the deviation, so the true exponent grows
near-linearly in `r` where the claimed bound grows as `r²`.  Hence small `α` (large prescribed `r`)
is the dangerous corner, and `c_eff` crosses *any* fixed constant for `r` large enough.

**So this file's refutation is not the strongest available statement.**  P-64 says the artifact's
formalization of Lemma 5 is false; P-67 says the paper's *use* of Lemma 5 is false on the paper's own
settings.  Neither touches the declarations below: `hnum ⟹ the registered bound` remains a theorem,
and the four `'`-forms remain correct.

## What is *proved* in this file

* `unionWitness_explicit` — the union-bound witness of `TSDPP.unionWitness`, made non-existential
  at the explicit `s = min 1 (29/(50ρ))`, and re-expressed in the `δ = ρ·s` parametrisation in
  which the one-sample tails produce their Chernoff factors.  `TSDPP/UnionBound.lean` states the
  witness existentially, which is not enough here: the lower-tail factor needs `δ < 1`, and only
  the explicit witness supplies it (`δ = ρ·min 1 (29/(50ρ)) ≤ 29/50`).  Its helper lemmas are
  `private` there, hence re-derived here.
* `betaMeasure_Ici_chernoff` / `betaMeasure_Iio_chernoff` — the two one-sample Beta tails of
  `TSDPP/BetaGammaChernoff.lean` with the **exact Chernoff optimisers**
  `u = δ(1+ρ)/((1+δ)(ρ-δ))`, `v = (1-δ)(1+ρ)/(δ(1+ρ-δ))` forced in, in closed form `A(δ)^α`,
  `B(δ)^α`.
* `betaMeasure_prod_abs_sub_le_small` — the **trivial branch**, unconditional: for
  `(11/100)·α·r² ≤ log 2` the estimate holds because the left-hand side is a probability.
* `betaMeasure_prod_abs_sub_le_union` — the **measure-theoretic core** of the two-sample bound:
  for any thresholds `t₁, t₂` with `t₁ - t₂ ≤ r·α/(α+β)`, exchangeability (`Measure.prod_swap`)
  plus the four-set cover
  `{rμ ≤ |p₁-p₂|} ⊆ ({t₁ ≤ p₁} ∪ {p₂ < t₂}) ∪ ({t₁ ≤ p₂} ∪ {p₁ < t₂})`
  give `Pr ≤ 2·(μ(Ici t₁) + μ(Iio t₂))`.  **This is exactly where `r ≥ 1` enters**: the lemma
  itself carries only `hst : t₁ - t₂ ≤ s`, and `1 ≤ r` is what licenses `t₁ - t₂ = μ(1+δ₁) - μδ ≤ rμ`
  for the small tails that make the two Chernoff factors informative.  See P-64: that same
  requirement is why the split cannot be run on the paper's `0 ≤ r ≤ 1` range, and why on `r ≥ 1`
  it produces a *true* implication whose antecedent `hnum` is nonetheless false outside the
  vacuous region `ρ ≤ r-1`.
* `betaMeasure_prod_abs_sub_le_unionTail` — the **union-bound branch**: at `t₁ = μ(1+δ₁)`,
  `t₂ = μδ` (any `0 < δ₁ < ρ`, `0 < δ < 1`, `δ₁ ≤ r-1+δ`), the two exact one-sample tails turn the
  reduction into
  `Pr ≤ 2·(A(δ₁)^α + B(δ)^α)`, and the target follows from the **explicit arithmetic residual**
  `hnum : A(δ₁)^α + B(δ)^α ≤ exp(-(11/100)·α·r²)`.  No measure theory is left in this step.
* `betaMeasure_Ici_chernoff'`, `betaMeasure_Iio_chernoff'`,
  `betaMeasure_prod_abs_sub_le_small'`, `betaMeasure_prod_abs_sub_le_unionTail'` — the same four
  results with the `hmap` hypothesis **discharged** from `TSDPP.gamma_ratio_isBetaMeasure`
  (`TSDPP/GammaRatioMap.lean`, read-only here).

## What is *not* proved here, and why (no papering over)

**The top-level target is not proved in this file — it is FALSE as registered** (see P-64 at the top
of this header: `(α,β,r) = (2,200,10)` gives LHS `8.6066e−09` against RHS `2e^{−22} = 5.5790e−10`;
the `2.789e−10` quoted further down is `e^{−22}`, the per-tail requirement, not this bound).  Everything
reduces to `hnum`, which is *not*
implied by `TSDPP.unionWitness`'s `exp(-(11/100))`: that constant is exactly the target's, and the
union bound pays for *both* tails (`A` and `B` each cost a factor, and the exchangeability factor
`2` an overall one), so the witness statement exposes no slack.  Concretely, the residual needs a
*sharper* margin than the witness gives, and this is where the file stops:

* with the one-sample shape `δ₁ = δ = 29/50` (the balanced optimum of the two factors, where
  `-log A ≈ 0.1225`, `-log B ≈ 0.1247` at `ρ → ∞`), `hnum` holds for `r ≤ 1.055` provided
  `α ≳ 56` — a genuine gap above the trivial branch's `α·r² ≤ 6.3014`;
* with the interpolated shape `δ₁ = r-1+δ` the same numerics widen the union-bound region to
  `α·r² ≳ 11` **at small `ρ`**; but a numerically scanned window remains — e.g. `ρ ≳ 20`, `r = 1`,
  `α ∈ (24, 47)` — in which *neither* the union bound, *nor* the trivial branch, *nor* the
  one-sided Cantelli/Chebyshev bound with the exact variance
  `Var(X) = αβ/((α+β)²(α+β+1))` suffices;

  **[CORRECTED 2026-09-17 — trap P-64.  The `α·r² ≳ 11` clause holds only at small `ρ` and must not
  be read as a region in `(α, r)` alone.]**  At `ρ = 100`, `r = 10` the required `α·r²` is `200`, yet
  the constrained infimum of `A(δ₁)^α + B(δ)^α` is `6.431e−7` against the needed `2.789e−10` — a
  2305× miss (`δ₁` pinned at `r−1 = 9` by `hrel`, `δ → 0`).  The large-`r` regime is not merely
  unscanned: it is where the antecedent is unsatisfiable, so no invariant in `(α, r)` alone can
  describe it.  `ρ` — absent from the claim as first written — is the third variable that matters;
* the window is an artefact of the union bound, not of the statement, and the obstruction is
  *method-level*, not arithmetic: the two factors satisfy, for **every** split `δ₁`,
  `A(δ₁)^α + B(δ₁)^α ≥ 2·(A(δ₁)B(δ₁))^{α/2} ≥ 2·0.883997^α` (AM–GM, using the method ceiling
  `min_δ max(A,B) = e/(e-1)·e^{-1/(e-1)} = 0.8839970429`, `-log = 0.123302`, recorded in
  `cards/L5.md` and `../DESIGN.md` GAP-2b/GAP-2c).  Hence `hnum` **provably fails** whenever
  `2·exp(-0.123302·α) > exp(-(11/100)·α·r²)`, i.e. for `α < log 2 / (0.123302 - 0.11·r²)`
  (`≈ 52` at `r = 1`).  So no choice of `δ₁`, `δ` and no refinement of the one-sample Chernoff
  bound closes the target below that `α` **[SUPERSEDED — trap P-62: the factor-`2` chain above is
  false at its second step, so "`hnum` provably fails" is withdrawn, and neither the `α`-threshold
  nor any replacement bound is derived by this argument; the bracketed correction at the end of this
  bullet now only retracts]** — the missing ingredient is
  a **joint** Chernoff bound on
  the pair of ratios (a four-fold Gamma product), which is a factor `≈ 2` better in the exponent
  (the true rate at `ρ → ∞`, `r = 1` is `≈ 0.25·α`, the difference of two `Gamma(α,1)`'s at the
  `√α` scale).  That joint estimate is not developed here, and the available
  `gammaMeasure_prod_lintegral_exp` is a two-fold product only.

  [CORRECTED 2026-09-17 — trap P-62.  The factor-`2` chain quoted above is **false at its second
  step** and the `α`-threshold derived from it is **not established**.  The two replacement bounds
  that were briefly recorded here are themselves **retracted**, so this block now subtracts only; the
  full three-layer record is `../DESIGN.md` trap P-62.

  * layer 1 (original): `A(δ₁)^α + B(δ₁)^α ≥ 2·(A(δ₁)B(δ₁))^{α/2} ≥ 2·0.883997^α` is AM–GM plus a
    second step needing `A(δ₁)B(δ₁) ≥ 0.883997²`, which fails as `δ₁ → 0` (`A → 1`, `B → 0`) —
    false.  The claimed bound also sits *above* the true `min_δ (A^α+B^α)` (`1.5629` vs `1.0000` at
    `α = 2`; `0.24586` vs `0.18180` at `α = 17`), so it is not a bound.
  * layer 2: `max(A(δ₁),B(δ₁)) ≥ m` with `m = inf_δ max(A,B) = 0.8839970429` — **[RETRACTED]**.
    `0.8839970429` is `sup_ρ min_δ max`, and `min_δ max(A_ρ,B_ρ)` increases with `ρ` (`0.603256`,
    `0.750000`, `0.819143`, `0.858599`, `0.871389`, `0.882745` at `ρ = 0.5, 1, 2, 5, 10, 100`;
    limit `0.8839970429`), so it is not a lower bound at finite `ρ`; the replacement also wrote
    `hnum`'s two independent arguments (`δ₁` in `chernoffA`, `δ` in `chernoffB`) as one `δ₁`.
  * layer 3: the per-`ρ` ceiling `r ≤ sqrt(-log m(ρ)/(11/100))` (values `2.1435`, `1.6172`,
    `1.3467`, `1.1773`, `1.0889`, `1.0648`, `1.0587`) — **[RETRACTED — 该替换使用了对称切片的一维
    下界,对 `hnum` 无效]**.  It used the diagonal slice `δ₁ = δ` (plus `B` monotone, valid only at
    `r = 1`), whereas `hnum` quantifies over the **two-dimensional** admissible set of pairs
    `(δ₁, δ)` linked only by `hrel : δ₁ ≤ r-1+δ`.  On that set the infimum **collapses to `0`**
    whenever `ρ ≤ r-1` (take `δ₁ → ρ⁻`, so `A(δ₁) → 0`, and `δ → 0`, so `B(δ) → 0`), so `hnum` is
    satisfiable for arbitrarily large `r`: **this route gives no upper bound on `r` at all.**

    **Two guards on that last sentence — trap `P-63`.**  (i) The collapse set is *not* merely
    "`ρ ≲ r-1`".  Writing `s := r/(1+ρ)` for the **event level** (the conclusion bounds
    `Pr(|X-Y| ≥ s)`), the event is *empty* exactly when `r ≥ 1+ρ`, i.e. `ρ ≤ r-1`: the collapse
    set and the empty-event set are **the same inequality**, so every witness of the collapse is a
    witness on which the conclusion has no content.  That does not weaken the sentence above —
    `hnum` really is satisfiable for every `r ≥ 1` — but the collapse is *not* evidence that the
    union-bound method is strong at large `r`; it is strong only where the target is vacuous.
    (ii) For a **fixed** cap `s ≤ s₀ < 1` on the event level there *is* a ceiling, and it diverges as
    `s₀ → 1`: `r*(s₀) = 6.159`, `8.554`, `12.138`, `20.460`, `40.187`, `61.073` at
    `s₀ = 0.3`, `0.5`, `0.7`, `0.9`, `0.99`, `0.999` (largest root of `G(r,s₀) = 0.11 r²` with
    `G(r,s) = -log r - ((r-s)/s)·log(r(1-s)/(r-s))` = `-log A(r-1)`, the branch `δ → 0`; an
    `α → ∞` indicator, not a theorem — finite `α` has `log 2/α` slack).  The honest form is: **no
    absolute ceiling; whatever ceiling there is is bought entirely with vacuity.**  It is bought by
    `ρ` approaching `r-1` from above, i.e. by the tail event approaching a null set — *not* by the
    paper's `r ≥ 1`, which constrains nothing here.
    Precisely: the vacuity criterion is `μ E = 0`, **not** `E = ∅`.  On the boundary `r = 1+ρ` the
    event `{|X-Y| ≥ 1}` is `{(0,1),(1,0)}` — non-empty, but null for `Beta(α,β)` with `α, β > 0`.
    So the correct equivalence chain is `μ E = 0 ⟺ r ≥ 1+ρ ⟺ ρ ≤ r-1`, and this is stronger than
    what the argument needs (it only ever used nullity).
    (iii) Retracted with layer 3: the claim that on `ρ > r-1` the constrained infimum *is* `m(ρ)`.
    It is not.  The constraint is slack, because `δ₁` may exceed `δ` by as much as `r-1`, so `A`
    can be evaluated at `r-1+δ`: at `ρ = 10`, `r = 1.1` (event level `s = 0.1`, far from vacuous)
    the explicit admissible pair `δ₁ = 0.6`, `δ = 0.5` (`hrel`: `0.6 ≤ 1.1-1+0.5`) gives
    `max = 0.861784`, and the true constrained infimum is `0.846523` — both **below**
    `m(10) = 0.871389`.  So `m(ρ)` bounds the constrained infimum from neither side, and no ceiling
    may be derived from it.
  * `c₀ = 11/100` is **[UNDERIVED — 常数依据待独立重导]**: its `α ≈ 52` ancestor is downstream of
    layer 1 and layer 3's uniformity argument is retracted, so no derivation is offered.

  The union-bound branch therefore establishes exactly the conditional of
  `betaMeasure_prod_abs_sub_le_unionTail` — the target follows from `hnum` — and says nothing about
  which `(ρ, α, r)` admit `hnum`.  The target is **not** proved here.]
* The constant `11/100` is thus *not certified* for all `α, β, r` by this file — and it is now known
  not to be **true** for all of them.  An earlier revision of this bullet asserted the statement was
  "numerically true on every grid tested (worst `bound/target` ratio `≤ 1`)".  **[RETRACTED — trap
  P-64.]**  That grid was `ρ`-balanced and never left `r ≲ 1`, so it could not see the failure; the
  worst cell it found was also `c`-independent, i.e. it was measuring the trivial branch.  At
  `(α,β,r) = (2,200,10)` (`ρ = 100`) the exact probability exceeds the registered bound by 15.4×, and
  the margin grows with `α`.  See `cards/L5.md`'s P-64 section for the same retraction applied there.
  What survives is the *conditional*: `hnum ⟹ the registered bound`, plus the fact that `hnum` is
  satisfiable on `r ≥ 1` only through the vacuous region `ρ ≤ r-1`.  On the paper's own range
  `0 ≤ r ≤ 1` the statement does appear true (`min c_eff = 0.242848 > 1/8` over the sweep recorded in
  P-64), but this file's toolkit cannot reach that range: the union split requires `r ≥ 1`, and the
  Gamma-Markov one-sample bound degenerates to 1 once the threshold sits at or below the mean
  (`rμ ≤ μ ⟺ r ≤ 1`).  Closing the paper's Lemma 5 needs exact incomplete-beta tails, which
  `GAP-2c` excludes.  Recorded as open, not papered over.

Every declaration below is closed by an explicit proof term; no goal is left open, no `axiom` and
no `opaque` is introduced, and nothing below depends on anything beyond
`propext, Classical.choice, Quot.sound` (machine-checked by `scripts/check_axioms.sh`).
-/
import TSDPP.BetaGammaChernoff
import TSDPP.UnionBound
import TSDPP.GammaRatioMap

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TSDPP

/-! ## 0. Elementary exponential estimates

`TSDPP/UnionBound.lean` carries these as `private` lemmas.  `private` declarations are file-scoped
in Lean 4 (their mangled names are not importable), so the explicit witness below needs its own
copies; the proofs are those of `TSDPP/UnionBound.lean` verbatim. -/

private lemma rpow_one_sub_div_le_exp_neg {n t : ℝ} (hn : 0 < n) (htn : t ≤ n) :
    (1 - t / n) ^ n ≤ Real.exp (-t) := by
  have hb : 0 ≤ 1 - t / n := sub_nonneg.2 ((div_le_one hn).2 htn)
  rcases hb.eq_or_lt with h | h
  · rw [← h, Real.zero_rpow (ne_of_gt hn)]
    exact (Real.exp_pos (-t)).le
  · have hlog := Real.log_le_sub_one_of_pos h
    have h4 : Real.log (1 - t / n) * n ≤ -t := by
      have hm := mul_le_mul_of_nonneg_right hlog hn.le
      have hthis : ((1 - t / n) - 1) * n = -t := by field_simp; ring
      linarith
    rw [Real.rpow_def_of_pos h]
    exact Real.exp_le_exp.2 h4

private lemma rpow_one_add_div_le_exp {n t : ℝ} (hn : 0 < n) (ht : 0 ≤ t) :
    (1 + t / n) ^ n ≤ Real.exp t := by
  have hb : 0 < 1 + t / n := by
    have : 0 ≤ t / n := div_nonneg ht hn.le
    linarith
  have hlog := Real.log_le_sub_one_of_pos hb
  have h4 : Real.log (1 + t / n) * n ≤ t := by
    have hm := mul_le_mul_of_nonneg_right hlog hn.le
    have hthis : ((1 + t / n) - 1) * n = t := by field_simp; ring
    linarith
  rw [Real.rpow_def_of_pos hb]
  exact Real.exp_le_exp.2 h4

private lemma mul_inv_rpow' (x y : ℝ) (hx : 0 < x) : x * (1 / x) ^ y = x ^ (1 - y) := by
  rw [Real.rpow_sub hx, Real.rpow_one, one_div, Real.inv_rpow hx.le, div_eq_mul_inv]

/-- `79/50 ≤ exp(47/100)`, from the 4th partial sum of `exp`. -/
private lemma numA_aux' : (1 + 29/50 : ℝ) ≤ Real.exp (47/100) := by
  have h := Real.sum_le_exp_of_nonneg (x := (47 : ℝ) / 100) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `(1 + 29/50) * exp(-(29/50)) ≤ exp(-(11/100))`; margin 1.26%. -/
private lemma numA' : (1 + 29/50 : ℝ) * Real.exp (-(29/50)) ≤ Real.exp (-(11/100)) := by
  have hp : (0 : ℝ) < Real.exp (29/50) := Real.exp_pos _
  have key : (1 + 29/50 : ℝ) ≤ Real.exp (-(11/100)) * Real.exp (29/50) := by
    rw [← Real.exp_add]
    have harg : -((11 : ℝ) / 100) + 29/50 = 47/100 := by norm_num
    rw [harg]
    exact numA_aux'
  calc (1 + 29/50 : ℝ) * Real.exp (-(29/50))
      = (1 + 29/50) / Real.exp (29/50) := by rw [Real.exp_neg]; rfl
    _ ≤ Real.exp (-(11/100)) := (div_le_iff₀ hp).2 key

/-- `exp(53/100) ≤ 50/29`, from the 4th partial sum plus the `exp_bound'` remainder. -/
private lemma numB_aux' : Real.exp (53/100) ≤ 50/29 := by
  have h := Real.exp_bound' (x := (53 : ℝ) / 100) (by norm_num) (by norm_num) (n := 4)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `29/50 ≤ exp(-(53/100))`, i.e. `exp(53/100) ≤ 50/29`. -/
private lemma numB1' : (29/50 : ℝ) ≤ Real.exp (-(53/100)) := by
  rw [Real.exp_neg, inv_eq_one_div, le_div_iff₀ (Real.exp_pos (53/100))]
  nlinarith [numB_aux']

/-- `(29/50) * exp(21/50) ≤ exp(-(11/100))`; margin 1.48%. -/
private lemma numB' : (29/50 : ℝ) * Real.exp (21/50) ≤ Real.exp (-(11/100)) := by
  have h := mul_le_mul_of_nonneg_right numB1' (Real.exp_pos (21/50)).le
  have harg : -((53 : ℝ) / 100) + 21/50 = -((11 : ℝ) / 100) := by norm_num
  rwa [← Real.exp_add, harg] at h

/-! ## 1. The two Chernoff factors and the explicit union-bound witness -/

/-- Upper-tail Chernoff factor at relative deviation `δ`, for `ρ = β/α`: the exact value of
`(1 - u(1-t))^(-α) * (1 + u t)^(-β)` at the optimiser `u` for the threshold `t = μ(1+δ)`, where
`μ = α/(α+β)`.  Valid for `0 < δ`; the underlying tail is meaningful for `δ < ρ`. -/
noncomputable def chernoffA (ρ δ : ℝ) : ℝ := (1 + δ) * (1 - δ / ρ) ^ ρ

/-- Lower-tail Chernoff factor at relative deviation `δ`: the exact value of
`(1 + v(1-t))^(-α) * (1 - v t)^(-β)` at the optimiser `v` for the threshold `t = μδ`.  Valid for
`0 < δ < 1` (for `δ > 1` the threshold lies above the mean and the optimiser is negative). -/
noncomputable def chernoffB (ρ δ : ℝ) : ℝ := δ * (1 + (1 - δ) / ρ) ^ ρ

/-- The union-bound witness of `TSDPP.unionWitness` at the explicit `s = min 1 (29/(50ρ))`,
restated in the `δ = ρ·s` parametrisation: at `δ = ρ·min 1 (29/(50ρ))` both Chernoff factors are
`≤ exp(-(11/100))`, and `δ ≤ 29/50 < 1` (so the lower-tail factor is the valid one). -/
theorem unionWitness_explicit (ρ : ℝ) (hρ : 0 < ρ) :
    0 < min 1 (29 / (50 * ρ)) ∧ min 1 (29 / (50 * ρ)) ≤ 1 ∧
      ρ * min 1 (29 / (50 * ρ)) ≤ 29 / 50 ∧
      chernoffA ρ (ρ * min 1 (29 / (50 * ρ))) ≤ Real.exp (-(11/100)) ∧
      chernoffB ρ (ρ * min 1 (29 / (50 * ρ))) ≤ Real.exp (-(11/100)) := by
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  have hs0 : 0 < min 1 (29 / (50 * ρ)) := lt_min one_pos (by positivity)
  have hs1 : min 1 (29 / (50 * ρ)) ≤ 1 := min_le_left _ _
  have hA : (1 + ρ * min 1 (29 / (50 * ρ))) * (1 - min 1 (29 / (50 * ρ))) ^ ρ
      ≤ Real.exp (-(11/100)) := by
    rcases le_or_gt (29 / (50 * ρ)) 1 with h | h
    · rw [min_eq_right h]
      have h50 : 29 ≤ 50 * ρ := (div_le_one (by positivity : (0 : ℝ) < 50 * ρ)).1 h
      have hge : (29 : ℝ) / 50 ≤ ρ := by linarith
      have hs : (29 : ℝ) / (50 * ρ) = (29/50) / ρ := by ring
      have hA1 : ρ * (29 / (50 * ρ)) = 29/50 := by field_simp; try ring
      rw [hA1, hs]
      have hle : (1 - (29/50) / ρ) ^ ρ ≤ Real.exp (-(29/50)) :=
        rpow_one_sub_div_le_exp_neg hρ hge
      exact (mul_le_mul_of_nonneg_left hle (by norm_num : (0 : ℝ) ≤ 1 + 29/50)).trans numA'
    · rw [min_eq_left h.le]
      have h0 : (1 - 1 : ℝ) ^ ρ = 0 := by rw [sub_self, Real.zero_rpow hρne]
      rw [mul_one, h0, mul_zero]
      exact (Real.exp_pos _).le
  have hB : (ρ * min 1 (29 / (50 * ρ))) * (1 / ρ + 1 - min 1 (29 / (50 * ρ))) ^ ρ
      ≤ Real.exp (-(11/100)) := by
    rcases le_or_gt (29 / (50 * ρ)) 1 with h | h
    · rw [min_eq_right h]
      have h50 : 29 ≤ 50 * ρ := (div_le_one (by positivity : (0 : ℝ) < 50 * ρ)).1 h
      have hge : (29 : ℝ) / 50 ≤ ρ := by linarith
      have hs : (29 : ℝ) / (50 * ρ) = (29/50) / ρ := by ring
      have hA1 : ρ * (29 / (50 * ρ)) = 29/50 := by field_simp; try ring
      rw [hA1, hs]
      have hbase : 1 / ρ + 1 - (29/50) / ρ = 1 + (21/50) / ρ := by ring
      rw [hbase]
      have hle2 : (1 + (21/50) / ρ) ^ ρ ≤ Real.exp (21/50) :=
        rpow_one_add_div_le_exp hρ (by norm_num)
      exact (mul_le_mul_of_nonneg_left hle2 (by norm_num : (0 : ℝ) ≤ 29/50)).trans numB'
    · rw [min_eq_left h.le]
      have h29 : 50 * ρ ≤ 29 := (one_le_div (by positivity : (0 : ℝ) < 50 * ρ)).1 h.le
      have hle : ρ ≤ 29/50 := by linarith
      have hbase : 1 / ρ + 1 - 1 = 1 / ρ := by ring
      rw [mul_one, hbase, mul_inv_rpow' ρ ρ hρ]
      have h1m' : (21 : ℝ) / 50 ≤ 1 - ρ := by linarith
      have hbound : Real.log ρ * (1 - ρ) ≤ -((21 : ℝ) / 50) ^ 2 := by
        have hlog := Real.log_le_sub_one_of_pos hρ
        have hm : Real.log ρ * (1 - ρ) ≤ (ρ - 1) * (1 - ρ) :=
          mul_le_mul_of_nonneg_right hlog (by linarith : (0 : ℝ) ≤ 1 - ρ)
        have h2 : (ρ - 1) * (1 - ρ) = -((1 - ρ) ^ 2) := by ring
        have h3 : ((21 : ℝ) / 50) ^ 2 ≤ (1 - ρ) ^ 2 := by
          nlinarith [sq_nonneg ((1 - ρ) - 21/50), h1m']
        linarith
      calc ρ ^ (1 - ρ) = Real.exp (Real.log ρ * (1 - ρ)) := Real.rpow_def_of_pos hρ _
        _ ≤ Real.exp (-((21 : ℝ) / 50) ^ 2) := Real.exp_le_exp.2 hbound
        _ ≤ Real.exp (-(11/100)) := by
              apply Real.exp_le_exp.2
              norm_num
  have hle : ρ * min 1 (29 / (50 * ρ)) ≤ 29 / 50 := by
    have h29 : min 1 (29 / (50 * ρ)) ≤ 29 / (50 * ρ) := min_le_right _ _
    calc ρ * min 1 (29 / (50 * ρ)) ≤ ρ * (29 / (50 * ρ)) :=
          mul_le_mul_of_nonneg_left h29 hρ.le
      _ = 29 / 50 := by field_simp
  refine ⟨hs0, hs1, hle, ?_, ?_⟩
  · rw [chernoffA]
    have hdiv : (ρ * min 1 (29 / (50 * ρ))) / ρ = min 1 (29 / (50 * ρ)) := by
      field_simp
    rw [hdiv]
    exact hA
  · rw [chernoffB]
    have hdiv : (1 - ρ * min 1 (29 / (50 * ρ))) / ρ
        = 1 / ρ - min 1 (29 / (50 * ρ)) := by
      field_simp
    rw [hdiv]
    have hre : 1 + (1 / ρ - min 1 (29 / (50 * ρ)))
        = 1 / ρ + 1 - min 1 (29 / (50 * ρ)) := by ring
    rw [hre]
    exact hB

/-! ## 2. The two one-sample tails at the exact Chernoff optimisers -/

/-- `x^β = (x^(β/α))^α` for `x ≥ 0`, `α ≠ 0`: the `ρ = β/α` re-parametrisation of the Gamma
exponent, which is what turns the two-factor Markov bound into a single `α`-th power. -/
private lemma rpow_beta_eq {α β : ℝ} (hα : α ≠ 0) {x : ℝ} (hx : 0 ≤ x) :
    x ^ β = (x ^ (β / α)) ^ α := by
  rw [← Real.rpow_mul hx (β / α) α, show β / α * α = β by field_simp]

/-- **Upper one-sample Beta tail, exact optimiser.**  With `ρ = β/α`, `μ = α/(α+β)` and
`0 < δ < ρ`, the choice `u = δ(1+ρ)/((1+δ)(ρ-δ))` gives `u(1-μ(1+δ)) = δ/(1+δ)` and
`u·μ(1+δ) = δ/(ρ-δ)`, so the Markov–Chernoff bound of `betaMeasure_Ici_le` collapses to
`A(δ)^α`, `A(δ) = (1+δ)(1-δ/ρ)^ρ` — the upper-tail factor of `TSDPP.unionWitness`.

`u` is used in the α-cleared form `δ(α+β)/((1+δ)(β-δα))` (the same number): `field_simp` cannot
clear the nested `β/α` divisions of the canonical form. -/
theorem betaMeasure_Ici_chernoff {α β δ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hδ : 0 < δ) (hδρ : δ < β / α)
    (hmap : betaMeasure α β = ((gammaMeasure α 1).prod (gammaMeasure β 1)).map
              (fun p : ℝ × ℝ => p.1 / (p.1 + p.2))) :
    betaMeasure α β (Set.Ici (α / (α + β) * (1 + δ)))
      ≤ ENNReal.ofReal ((chernoffA (β / α) δ) ^ α) := by
  have hαβ : 0 < α + β := by linarith
  have h1δ : 0 < 1 + δ := by linarith
  have hρ : 0 < β / α := div_pos hβ hα
  have hβδα : 0 < β - δ * α := by
    have h := (lt_div_iff₀ hα).1 hδρ
    linarith
  set u : ℝ := δ * (α + β) / ((1 + δ) * (β - δ * α)) with hu_def
  set t : ℝ := α / (α + β) * (1 + δ) with ht_def
  have hu : 0 < u := by rw [hu_def]; positivity
  have ht : 0 < t := by rw [ht_def]; positivity
  have hu1t : u * (1 - t) = δ / (1 + δ) := by
    rw [hu_def, ht_def]
    field_simp
    ring
  have hut : u * t = δ * α / (β - δ * α) := by
    rw [hu_def, ht_def]
    field_simp
  have hu1 : u * (1 - t) < 1 := by
    rw [hu1t, div_lt_one h1δ]
    linarith
  have h := betaMeasure_Ici_le hα hβ hu ht hu1 hmap
  have hbase : 0 ≤ 1 - δ / (β / α) := by
    have h1 : δ / (β / α) < 1 := (div_lt_one hρ).2 hδρ
    linarith
  have hkey : (1 - u * (1 - t)) ^ (-α) * (1 + u * t) ^ (-β)
      = (chernoffA (β / α) δ) ^ α := by
    rw [hu1t, hut]
    have h1 : 1 - δ / (1 + δ) = (1 + δ)⁻¹ := by field_simp; ring_nf
    have h2 : 1 + δ * α / (β - δ * α) = (1 - δ / (β / α))⁻¹ := by
      field_simp
      ring_nf
    rw [h1, h2]
    rw [Real.inv_rpow h1δ.le, Real.rpow_neg h1δ.le, inv_inv,
      Real.inv_rpow hbase, Real.rpow_neg hbase, inv_inv]
    rw [rpow_beta_eq (ne_of_gt hα) hbase, chernoffA,
      ← Real.mul_rpow h1δ.le (Real.rpow_nonneg hbase (β / α))]
  calc betaMeasure α β (Set.Ici (α / (α + β) * (1 + δ)))
      = betaMeasure α β (Set.Ici t) := by rw [ht_def]
    _ ≤ ENNReal.ofReal ((1 - u * (1 - t)) ^ (-α) * (1 + u * t) ^ (-β)) := h
    _ = ENNReal.ofReal ((chernoffA (β / α) δ) ^ α) := by rw [hkey]

/-- **Lower one-sample Beta tail, exact optimiser.**  With `ρ = β/α`, `μ = α/(α+β)` and
`0 < δ < 1` (the threshold `μδ` must lie below the mean: for `δ > 1` the optimiser is negative and
the Chernoff bound degenerates to the trivial `1`), the choice
`v = (1-δ)(1+ρ)/(δ(1+ρ-δ))` gives `1 + v(1-μδ) = 1/δ` and `1 - v·μδ = ρ/(1+ρ-δ)`, so the bound of
`betaMeasure_Iio_le` collapses to `B(δ)^α`, `B(δ) = δ(1+(1-δ)/ρ)^ρ` — the lower-tail factor of
`TSDPP.unionWitness`.  As above, `v` is used in the α-cleared form. -/
theorem betaMeasure_Iio_chernoff {α β δ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hmap : betaMeasure α β = ((gammaMeasure α 1).prod (gammaMeasure β 1)).map
              (fun p : ℝ × ℝ => p.1 / (p.1 + p.2))) :
    betaMeasure α β (Set.Iio (α / (α + β) * δ))
      ≤ ENNReal.ofReal ((chernoffB (β / α) δ) ^ α) := by
  have hαβ : 0 < α + β := by linarith
  have hρ : 0 < β / α := div_pos hβ hα
  have h1δ : 0 < 1 - δ := by linarith
  have hab : 0 < α + β - δ * α := by
    have : δ * α < 1 * α := by nlinarith
    linarith
  set v : ℝ := (1 - δ) * (α + β) / (δ * (α + β - δ * α)) with hv_def
  set t : ℝ := α / (α + β) * δ with ht_def
  have hv : 0 < v := by rw [hv_def]; positivity
  have ht1 : t < 1 := by
    rw [ht_def]
    have hμ : α / (α + β) ≤ 1 := (div_le_one hαβ).2 (by linarith)
    have h1 : α / (α + β) * δ ≤ 1 * δ := mul_le_mul_of_nonneg_right hμ hδ.le
    have h2 : (1 : ℝ) * δ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hδ1.le zero_le_one
    linarith
  have hvt : v * t = α * (1 - δ) / (α + β - δ * α) := by
    rw [hv_def, ht_def]
    field_simp
  have hvt1 : v * t < 1 := by
    rw [hvt, div_lt_one hab]
    nlinarith
  have h := betaMeasure_Iio_le hα hβ hv ht1 hvt1 hmap
  have hbase : 0 ≤ 1 + (1 - δ) / (β / α) := by
    have h1 : 0 ≤ (1 - δ) / (β / α) := div_nonneg h1δ.le hρ.le
    linarith
  have hkey : (1 + v * (1 - t)) ^ (-α) * (1 - v * t) ^ (-β)
      = (chernoffB (β / α) δ) ^ α := by
    rw [hvt]
    have h1 : 1 + v * (1 - t) = δ⁻¹ := by
      rw [hv_def, ht_def]
      field_simp
      ring_nf
    have h2 : 1 - α * (1 - δ) / (α + β - δ * α) = (1 + (1 - δ) / (β / α))⁻¹ := by
      have hA : α + β - δ * α ≠ 0 := ne_of_gt hab
      have hX : 1 - α * (1 - δ) / (α + β - δ * α) = β / (α + β - δ * α) := by
        rw [eq_div_iff hA, sub_mul, div_mul_cancel₀ _ hA, one_mul]
        ring
      have hY : 1 + (1 - δ) / (β / α) = (α + β - δ * α) / β := by
        rw [div_div_eq_mul_div, eq_div_iff (ne_of_gt hβ), add_mul, one_mul,
          div_mul_cancel₀ _ (ne_of_gt hβ)]
        ring
      rw [hX, hY, inv_div]
    rw [h1, h2]
    rw [Real.inv_rpow hδ.le, Real.rpow_neg hδ.le, inv_inv,
      Real.inv_rpow hbase, Real.rpow_neg hbase, inv_inv]
    rw [rpow_beta_eq (ne_of_gt hα) hbase, chernoffB,
      ← Real.mul_rpow hδ.le (Real.rpow_nonneg hbase (β / α))]
  calc betaMeasure α β (Set.Iio (α / (α + β) * δ))
      = betaMeasure α β (Set.Iio t) := by rw [ht_def]
    _ ≤ ENNReal.ofReal ((1 + v * (1 - t)) ^ (-α) * (1 - v * t) ^ (-β)) := h
    _ = ENNReal.ofReal ((chernoffB (β / α) δ) ^ α) := by rw [hkey]

/-! ## 3. The trivial branch: `0.11·α·r² ≤ log 2`

The product of two probability measures is a probability measure, so the event has measure at
most `1`, and `1 ≤ 2·exp(-0.11·α·r²)` is exactly `0.11·α·r² ≤ log 2`. -/

theorem betaMeasure_prod_abs_sub_le_small {α β r : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hsmall : (11/100) * α * r ^ 2 ≤ Real.log 2)
    (hmap : betaMeasure α β = ((gammaMeasure α 1).prod (gammaMeasure β 1)).map
              (fun p : ℝ × ℝ => p.1 / (p.1 + p.2))) :
    ((betaMeasure α β).prod (betaMeasure α β))
      {p : ℝ × ℝ | r * (α / (α + β)) ≤ |p.1 - p.2|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(11/100) * α * r ^ 2)) := by
  have hgα : IsProbabilityMeasure (gammaMeasure α 1) := isProbabilityMeasure_gammaMeasure hα one_pos
  have hgβ : IsProbabilityMeasure (gammaMeasure β 1) := isProbabilityMeasure_gammaMeasure hβ one_pos
  have hβp : IsProbabilityMeasure (betaMeasure α β) := by rw [hmap]; infer_instance
  have h1 : ((betaMeasure α β).prod (betaMeasure α β))
      {p : ℝ × ℝ | r * (α / (α + β)) ≤ |p.1 - p.2|} ≤ 1 :=
    (measure_mono (Set.subset_univ _)).trans (by rw [measure_univ])
  have h2 : (1 : ℝ) ≤ 2 * Real.exp (-(11/100) * α * r ^ 2) := by
    have h4 : Real.exp (-Real.log 2) = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    have h3 : Real.exp (-(Real.log 2)) ≤ Real.exp (-(11/100) * α * r ^ 2) := by
      apply Real.exp_le_exp.2
      linarith
    linarith
  calc ((betaMeasure α β).prod (betaMeasure α β))
        {p : ℝ × ℝ | r * (α / (α + β)) ≤ |p.1 - p.2|}
      ≤ 1 := h1
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(11/100) * α * r ^ 2)) := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal h2

/-! ## 4. The union-bound reduction (measure-theoretic core)

For a *product* measure with equal marginals, the two-sample event splits into four marginals:

  `{s ≤ |p₁ - p₂|} ⊆ ({t₁ ≤ p₁} ∪ {p₂ < t₂}) ∪ ({t₁ ≤ p₂} ∪ {p₁ < t₂})`

whenever `t₁ - t₂ ≤ s` (if all four complements hold then `p₁ - p₂ < t₁ - t₂ ≤ s` and
`p₂ - p₁ < t₁ - t₂ ≤ s`).  Both shapes used below are instances: the "one-sample" shape
`t₁ = μ(1+δ)`, `t₂ = μδ` gives `t₁ - t₂ = μ ≤ rμ` (uses `1 ≤ r`), and the interpolated shape
`t₁ = μ(r+δ)`, `t₂ = μδ` gives `t₁ - t₂ = rμ` exactly.  That `1 ≤ r` is the whole cost of the
method, and it is *not* removable — which is why the paper's `0 ≤ r ≤ 1` range cannot be reached
from here (P-64, and the header's route analysis). -/

theorem betaMeasure_prod_abs_sub_le_union {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    {s t₁ t₂ : ℝ} (hst : t₁ - t₂ ≤ s)
    (hmap : betaMeasure α β = ((gammaMeasure α 1).prod (gammaMeasure β 1)).map
              (fun p : ℝ × ℝ => p.1 / (p.1 + p.2))) :
    ((betaMeasure α β).prod (betaMeasure α β)) {p : ℝ × ℝ | s ≤ |p.1 - p.2|}
      ≤ 2 * ((betaMeasure α β) (Set.Ici t₁) + (betaMeasure α β) (Set.Iio t₂)) := by
  have hgα : IsProbabilityMeasure (gammaMeasure α 1) := isProbabilityMeasure_gammaMeasure hα one_pos
  have hgβ : IsProbabilityMeasure (gammaMeasure β 1) := isProbabilityMeasure_gammaMeasure hβ one_pos
  have hβp : IsProbabilityMeasure (betaMeasure α β) := by rw [hmap]; infer_instance
  have hsub : {p : ℝ × ℝ | s ≤ |p.1 - p.2|} ⊆
      ({p : ℝ × ℝ | t₁ ≤ p.1} ∪ {p : ℝ × ℝ | p.2 < t₂}) ∪
        ({p : ℝ × ℝ | t₁ ≤ p.2} ∪ {p : ℝ × ℝ | p.1 < t₂}) := by
    intro p hp
    simp only [Set.mem_ofPred_eq] at hp
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le, not_lt] at h
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
    have h5 : p.1 - p.2 < s := by linarith
    have h6 : p.2 - p.1 < s := by linarith
    have h7 : |p.1 - p.2| < s := abs_lt.2 ⟨by linarith, by linarith⟩
    linarith [h7, hp]
  have e1 : ((betaMeasure α β).prod (betaMeasure α β)) {p : ℝ × ℝ | t₁ ≤ p.1}
      = betaMeasure α β (Set.Ici t₁) := by
    have hs : {p : ℝ × ℝ | t₁ ≤ p.1} = Set.Ici t₁ ×ˢ Set.univ := by
      ext p; simp
    rw [hs, Measure.prod_prod, measure_univ, mul_one]
  have e2 : ((betaMeasure α β).prod (betaMeasure α β)) {p : ℝ × ℝ | p.2 < t₂}
      = betaMeasure α β (Set.Iio t₂) := by
    have hs : {p : ℝ × ℝ | p.2 < t₂} = Set.univ ×ˢ Set.Iio t₂ := by
      ext p; simp
    rw [hs, Measure.prod_prod, measure_univ, one_mul]
  have e3 : ((betaMeasure α β).prod (betaMeasure α β)) {p : ℝ × ℝ | t₁ ≤ p.2}
      = betaMeasure α β (Set.Ici t₁) := by
    have hs : {p : ℝ × ℝ | t₁ ≤ p.2} = Set.univ ×ˢ Set.Ici t₁ := by
      ext p; simp
    rw [hs, Measure.prod_prod, measure_univ, one_mul]
  have e4 : ((betaMeasure α β).prod (betaMeasure α β)) {p : ℝ × ℝ | p.1 < t₂}
      = betaMeasure α β (Set.Iio t₂) := by
    have hs : {p : ℝ × ℝ | p.1 < t₂} = Set.Iio t₂ ×ˢ Set.univ := by
      ext p; simp
    rw [hs, Measure.prod_prod, measure_univ, mul_one]
  calc ((betaMeasure α β).prod (betaMeasure α β)) {p : ℝ × ℝ | s ≤ |p.1 - p.2|}
      ≤ ((betaMeasure α β).prod (betaMeasure α β))
          (({p : ℝ × ℝ | t₁ ≤ p.1} ∪ {p : ℝ × ℝ | p.2 < t₂}) ∪
            ({p : ℝ × ℝ | t₁ ≤ p.2} ∪ {p : ℝ × ℝ | p.1 < t₂})) := measure_mono hsub
    _ ≤ ((betaMeasure α β).prod (betaMeasure α β))
          ({p : ℝ × ℝ | t₁ ≤ p.1} ∪ {p : ℝ × ℝ | p.2 < t₂})
        + ((betaMeasure α β).prod (betaMeasure α β))
          ({p : ℝ × ℝ | t₁ ≤ p.2} ∪ {p : ℝ × ℝ | p.1 < t₂}) := measure_union_le _ _
    _ ≤ (((betaMeasure α β).prod (betaMeasure α β)) {p : ℝ × ℝ | t₁ ≤ p.1}
          + ((betaMeasure α β).prod (betaMeasure α β)) {p : ℝ × ℝ | p.2 < t₂})
        + (((betaMeasure α β).prod (betaMeasure α β)) {p : ℝ × ℝ | t₁ ≤ p.2}
          + ((betaMeasure α β).prod (betaMeasure α β)) {p : ℝ × ℝ | p.1 < t₂}) := by
        gcongr <;> exact measure_union_le _ _
    _ = 2 * ((betaMeasure α β) (Set.Ici t₁) + (betaMeasure α β) (Set.Iio t₂)) := by
        rw [e1, e2, e3, e4]; ring

/-! ## 5. The union-bound branch of the target

For any `δ₁ ∈ (0,ρ)`, `δ ∈ (0,1)` with `δ₁ ≤ r-1+δ` (so `t₁ = μ(1+δ₁)`, `t₂ = μδ` satisfy
`t₁ - t₂ = μ(1+δ₁-δ) ≤ rμ`), the reduction of §4 plus the two tails of §2 give

  `Pr(|X-Y| ≥ rμ) ≤ 2·(A(δ₁)^α + B(δ)^α)`.

The whole content of Lemma 5/Eq (31) beyond this point is the **arithmetic** inequality `hnum`
below.  It is *not* implied by `TSDPP.unionWitness`'s `exp(-11/100)`: the bound
`A(δ₁)^α + B(δ)^α ≤ exp(-0.11·α·r²)` at `δ₁ = δ = 29/50` is exactly the point where the witness's
`c₀ = 11/100` has been designed to be *tight*, and both tails must be paid for, so `hnum` needs a
sharper margin than the witness statement exposes.  Two shapes of `hnum` are classically used:
`δ₁ = δ` (one-sample shape, needs `r ≥ 1`) and `δ₁ = r-1+δ` (interpolated shape).

**[CORRECTED 2026-09-17 — trap P-64.  This docstring previously read: "numerically: `hnum` holds for
`r ≤ 1.055` with `α ≳ 56`, and, with `δ₁ = r-1+δ`, for all `ρ > 0` once `α·r² ≥ ~11`; ... the second
being strictly stronger away from `r = 1`."]**  Both claims are withdrawn, and the second is false as
stated: `α·r² ≥ 11` does **not** suffice for all `ρ`.  At `ρ = 100`, `r = 10` we have `α·r² = 200`,
and the constrained infimum is still a 2305× miss (`6.431e−7` vs `2.789e−10`).  The `δ₁ ≤ r-1+δ`
constraint *ties the split to `r`*: `δ₁` can reach `r−1` at best, so the antecedent only becomes
satisfiable where the two tails can simultaneously be small, i.e. where `r` is large enough — which
is exactly where the registered bound is false.  **There is no region described by `(α, r)` alone on
which `hnum` holds non-vacuously.**  The residual is now stated without a region claim: it is the
explicit hypothesis `hnum`, and the header records which `(ρ, α, r)` refute the registered target.
The `hnum ⟹ bound` implication proved below is unaffected and remains the file's real content. -/

theorem betaMeasure_prod_abs_sub_le_unionTail {α β r δ₁ δ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (_hr : 1 ≤ r) (hδ₁0 : 0 < δ₁) (hδ₁ρ : δ₁ < β / α) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hrel : δ₁ ≤ r - 1 + δ)
    (hnum : (chernoffA (β / α) δ₁) ^ α + (chernoffB (β / α) δ) ^ α
              ≤ Real.exp (-(11/100) * α * r ^ 2))
    (hmap : betaMeasure α β = ((gammaMeasure α 1).prod (gammaMeasure β 1)).map
              (fun p : ℝ × ℝ => p.1 / (p.1 + p.2))) :
    ((betaMeasure α β).prod (betaMeasure α β))
      {p : ℝ × ℝ | r * (α / (α + β)) ≤ |p.1 - p.2|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(11/100) * α * r ^ 2)) := by
  have hμpos : 0 < α / (α + β) := by positivity
  have hst : α / (α + β) * (1 + δ₁) - α / (α + β) * δ ≤ r * (α / (α + β)) := by
    have h : α / (α + β) * (1 + δ₁) - α / (α + β) * δ = α / (α + β) * (1 + (δ₁ - δ)) := by ring
    rw [h]
    have h2 : 1 + (δ₁ - δ) ≤ r := by linarith only [hrel]
    calc α / (α + β) * (1 + (δ₁ - δ)) ≤ α / (α + β) * r := mul_le_mul_of_nonneg_left h2 hμpos.le
      _ = r * (α / (α + β)) := by ring
  have hIci := betaMeasure_Ici_chernoff (α := α) (β := β) (δ := δ₁) hα hβ hδ₁0 hδ₁ρ hmap
  have hIio := betaMeasure_Iio_chernoff (α := α) (β := β) (δ := δ) hα hβ hδ0 hδ1 hmap
  have hA0 : (0 : ℝ) ≤ (chernoffA (β / α) δ₁) ^ α := by
    rw [chernoffA]
    have h : (0 : ℝ) ≤ 1 - δ₁ / (β / α) := by
      have h2 : δ₁ / (β / α) < 1 := (div_lt_one (by linarith : (0 : ℝ) < β / α)).2 hδ₁ρ
      linarith
    positivity
  have hB0 : (0 : ℝ) ≤ (chernoffB (β / α) δ) ^ α := by
    rw [chernoffB]; positivity
  calc ((betaMeasure α β).prod (betaMeasure α β))
        {p : ℝ × ℝ | r * (α / (α + β)) ≤ |p.1 - p.2|}
      ≤ 2 * ((betaMeasure α β) (Set.Ici (α / (α + β) * (1 + δ₁)))
              + (betaMeasure α β) (Set.Iio (α / (α + β) * δ))) :=
        betaMeasure_prod_abs_sub_le_union hα hβ hst hmap
    _ ≤ 2 * (ENNReal.ofReal ((chernoffA (β / α) δ₁) ^ α)
              + ENNReal.ofReal ((chernoffB (β / α) δ) ^ α)) := by gcongr
    _ = ENNReal.ofReal (2 * ((chernoffA (β / α) δ₁) ^ α + (chernoffB (β / α) δ) ^ α)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_add hA0 hB0,
          ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(11/100) * α * r ^ 2)) :=
        ENNReal.ofReal_le_ofReal (by linarith [hnum])

/-! ## 6. The `hmap` hypothesis discharged

`hmap` is not an independent assumption: `TSDPP.gamma_ratio_isBetaMeasure`
(`TSDPP/GammaRatioMap.lean`, in the build closure) proves exactly this statement, so every result
above is available with the map law discharged. -/

/-- The upper one-sample tail, `hmap` discharged. -/
theorem betaMeasure_Ici_chernoff' {α β δ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hδ : 0 < δ) (hδρ : δ < β / α) :
    betaMeasure α β (Set.Ici (α / (α + β) * (1 + δ)))
      ≤ ENNReal.ofReal ((chernoffA (β / α) δ) ^ α) :=
  betaMeasure_Ici_chernoff hα hβ hδ hδρ (gamma_ratio_isBetaMeasure hα hβ)

/-- The lower one-sample tail, `hmap` discharged. -/
theorem betaMeasure_Iio_chernoff' {α β δ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    betaMeasure α β (Set.Iio (α / (α + β) * δ))
      ≤ ENNReal.ofReal ((chernoffB (β / α) δ) ^ α) :=
  betaMeasure_Iio_chernoff hα hβ hδ hδ1 (gamma_ratio_isBetaMeasure hα hβ)

/-- The trivial branch, `hmap` discharged. -/
theorem betaMeasure_prod_abs_sub_le_small' {α β r : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hsmall : (11/100) * α * r ^ 2 ≤ Real.log 2) :
    ((betaMeasure α β).prod (betaMeasure α β))
      {p : ℝ × ℝ | r * (α / (α + β)) ≤ |p.1 - p.2|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(11/100) * α * r ^ 2)) :=
  betaMeasure_prod_abs_sub_le_small hα hβ hsmall (gamma_ratio_isBetaMeasure hα hβ)

/-- The union-bound branch, `hmap` discharged. -/
theorem betaMeasure_prod_abs_sub_le_unionTail' {α β r δ₁ δ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hr : 1 ≤ r) (hδ₁0 : 0 < δ₁) (hδ₁ρ : δ₁ < β / α) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hrel : δ₁ ≤ r - 1 + δ)
    (hnum : (chernoffA (β / α) δ₁) ^ α + (chernoffB (β / α) δ) ^ α
              ≤ Real.exp (-(11/100) * α * r ^ 2)) :
    ((betaMeasure α β).prod (betaMeasure α β))
      {p : ℝ × ℝ | r * (α / (α + β)) ≤ |p.1 - p.2|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(11/100) * α * r ^ 2)) :=
  betaMeasure_prod_abs_sub_le_unionTail hα hβ hr hδ₁0 hδ₁ρ hδ0 hδ1 hrel hnum
    (gamma_ratio_isBetaMeasure hα hβ)

end TSDPP
