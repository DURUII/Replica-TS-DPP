/-
Lemma 5 of the paper (Eq. (31)), on the paper's *own* range `0 ≤ r ≤ 1`.

Statement (paper.pdf p.9): if `X ~ Beta(α,β)` and `Y` is an independent copy then, for all
`0 ≤ r ≤ 1`,  `Pr(|X - Y| ≥ r·E X) ≤ 2·e^{-α r²/8}`,  where `E X = α/(α+β)`.

Route (NOT the artifact's union bound + Chernoff, which needs `1 ≤ r` and additionally fails in
the far tail; see DESIGN.md card P-64 and the autopsy below):

  Pr(|X-Y| ≥ rμ) ≤ Pr(X-Y ≥ rμ) + Pr(Y-X ≥ rμ) = 2·Pr(X-Y ≥ rμ)   [product symmetry]
                 ≤ 2·E[e^{λ(X-Y)}]·e^{-λrμ}                        [Markov, λ ≥ 0]
                 ≤ 2·e^{2αλ²/(α+β)²}·e^{-λrμ}                      [two-sided MGF bound]
                 = 2·e^{-αr²/8}                                     [λ := r(α+β)/4, r ≤ 1]

The last step needs `λ ≤ (α+β)/4`, i.e. exactly `r ≤ 1` — this is where the paper's range is
consumed, and it is disjoint from the artifact's `1 ≤ r` range.

Deliverables in this file
  * `betaMeasure_prod_abs_sub_le_of_mgf` — the full target on `0 ≤ r ≤ 1`, **conditional** on the
    single residual node `BetaProdMGFBound` (nothing else); `#print axioms` gives exactly
    `[propext, Classical.choice, Quot.sound]`.
  * `betaMeasure_prod_abs_sub_le_of_log2` — **unconditional**, but only where the claimed bound is
    `≥ 1` (`α r² ≤ 8 log 2`), i.e. the trivial half.
  * `BetaProdMGFBound` — the one un-discharged node (`(C)` ≡ `(T'')` in DESIGN.md).

Rejected routes (details and measurements in `Lemma5PaperRange.TRAPS.md` §B)
  * union bound + `chernoffA`/`chernoffB` (the artifact's toolkit): the Chernoff factors are loose
    by a *polynomial* factor 20-80x (3-4.4 nats) in the far tail `ρ = β/α ≫ 1`, and the loss grows
    with α; the union structure itself is fine (with exact tails the same instance lands at 0.035x
    of the target), so the bottleneck is the tail estimate, and the exact tail is an incomplete
    Beta / `₁F₁` which Mathlib does not have.
  * `(T'')`'s global sup is `16/9 = 1.7778 < 2`, approached only at `α → 0, β → ∞, u = (α+β)/4`;
    any proof of `(T'')` must be sharp to a factor ~1.12 there, so no "crude inequality plus slack"
    can close it.

No `sorry`, no `axiom`, no `native_decide`, no `unsafe`, no floats.
-/
import Mathlib
import TSDPP.BetaConcentration

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TSDPP

noncomputable section

/-- **Residual analytic core (isolated hypothesis).**

For `0 ≤ λ ≤ (α+β)/4` the difference `X - Y` of two independent `Beta(α,β)` variables satisfies
the two-sided sub-Gaussian MGF bound with proxy variance `2α/(α+β)²`.

This is `(C)` of DESIGN.md (equivalently `(T'')`: `Var_u(X) ≤ 2 Var(X)` for the exponentially
tilted law, `|u| ≤ (α+β)/4`). It is verified numerically (zero failures over 3780 cells, worst
ratio 0.49999 of budget) but is *not* proved here; it is the single un-discharged node.
Integrability is bundled because that is what the Markov step consumes. -/
def BetaProdMGFBound (α β : ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → t ≤ (α + β) / 4 →
    Integrable (fun p : ℝ × ℝ => Real.exp (t * (p.1 - p.2)))
        ((betaMeasure α β).prod (betaMeasure α β)) ∧
      (∫ p, Real.exp (t * (p.1 - p.2)) ∂((betaMeasure α β).prod (betaMeasure α β)))
        ≤ Real.exp (2 * α * t ^ 2 / (α + β) ^ 2)

/-- Lemma 5 of the paper on `0 ≤ r ≤ 1`, conditional on the (isolated, numerically verified)
two-sided MGF core `BetaProdMGFBound`. -/
theorem betaMeasure_prod_abs_sub_le_of_mgf {α β r : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hMGF : BetaProdMGFBound α β) :
    ((betaMeasure α β).prod (betaMeasure α β))
        {p : ℝ × ℝ | r * (α / (α + β)) ≤ |p.1 - p.2|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(1 / 8) * α * r ^ 2)) := by
  have hc : 0 < α + β := by linarith
  set μ : Measure ℝ := betaMeasure α β with hμdef
  haveI : IsProbabilityMeasure μ := isProbabilityMeasureBeta hα hβ
  set s : ℝ := r * (α / (α + β)) with hsdef
  -- (1) absolute value splits into the two one-sided events
  have hsub : {p : ℝ × ℝ | s ≤ |p.1 - p.2|} ⊆
      {p : ℝ × ℝ | s ≤ p.1 - p.2} ∪ {p : ℝ × ℝ | s ≤ p.2 - p.1} := by
    intro p hp
    simp only [Set.mem_union, Set.mem_ofPred_eq] at hp ⊢
    rcases le_abs.mp hp with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  -- (2) the two one-sided events have the same measure (product symmetry)
  have hmeas : MeasurableSet {p : ℝ × ℝ | s ≤ p.1 - p.2} :=
    (isClosed_le continuous_const (continuous_fst.sub continuous_snd)).measurableSet
  have hpre : Prod.swap ⁻¹' {p : ℝ × ℝ | s ≤ p.1 - p.2} =
      {p : ℝ × ℝ | s ≤ p.2 - p.1} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Prod.fst_swap, Prod.snd_swap]
  have hswap : (μ.prod μ) {p : ℝ × ℝ | s ≤ p.2 - p.1} =
      (μ.prod μ) {p : ℝ × ℝ | s ≤ p.1 - p.2} := by
    rw [← hpre, ← Measure.map_apply measurable_swap hmeas, Measure.prod_swap]
  have hstep1 : (μ.prod μ) {p : ℝ × ℝ | s ≤ |p.1 - p.2|}
      ≤ 2 * (μ.prod μ) {p : ℝ × ℝ | s ≤ p.1 - p.2} := by
    calc (μ.prod μ) {p : ℝ × ℝ | s ≤ |p.1 - p.2|}
        ≤ (μ.prod μ) ({p : ℝ × ℝ | s ≤ p.1 - p.2} ∪ {p : ℝ × ℝ | s ≤ p.2 - p.1}) :=
          measure_mono hsub
      _ ≤ (μ.prod μ) {p : ℝ × ℝ | s ≤ p.1 - p.2} + (μ.prod μ) {p : ℝ × ℝ | s ≤ p.2 - p.1} :=
          measure_union_le _ _
      _ = 2 * (μ.prod μ) {p : ℝ × ℝ | s ≤ p.1 - p.2} := by rw [hswap, two_mul]
  -- (3) Markov at the optimal tilt
  set lam : ℝ := r * (α + β) / 4 with hlamdef
  have hlam0 : 0 ≤ lam := by
    rw [hlamdef]; positivity
  have hlamle : lam ≤ (α + β) / 4 := by
    rw [hlamdef]; nlinarith
  obtain ⟨hint, hbound⟩ := hMGF lam hlam0 hlamle
  have hf_eq : ∀ p : ℝ × ℝ,
      Real.exp (lam * (p.1 - p.2 - s)) = Real.exp (-(lam * s)) * Real.exp (lam * (p.1 - p.2)) := by
    intro p
    rw [← Real.exp_add]
    congr 1
    ring
  have hsub2 : {p : ℝ × ℝ | s ≤ p.1 - p.2} ⊆
      {p : ℝ × ℝ | 1 ≤ Real.exp (lam * (p.1 - p.2 - s))} := by
    intro p hp
    simp only [Set.mem_ofPred_eq] at hp ⊢
    exact Real.one_le_exp (mul_nonneg hlam0 (by linarith))
  have hmarkov : (μ.prod μ).real {p : ℝ × ℝ | s ≤ p.1 - p.2}
      ≤ Real.exp (-(lam * s)) * Real.exp (2 * α * lam ^ 2 / (α + β) ^ 2) := by
    have h1 := mul_meas_ge_le_integral_of_nonneg
      (μ := μ.prod μ) (f := fun p : ℝ × ℝ => Real.exp (lam * (p.1 - p.2 - s)))
      (Filter.Eventually.of_forall fun p => Real.exp_nonneg _)
      (by simpa only [hf_eq] using hint.const_mul (Real.exp (-(lam * s)))) 1
    rw [one_mul] at h1
    have h2 : (μ.prod μ).real {p : ℝ × ℝ | s ≤ p.1 - p.2}
        ≤ (μ.prod μ).real {p : ℝ × ℝ | 1 ≤ Real.exp (lam * (p.1 - p.2 - s))} :=
      measureReal_mono hsub2
    refine le_trans h2 (le_trans h1 ?_)
    simp only [hf_eq, integral_const_mul]
    exact mul_le_mul_of_nonneg_left hbound (Real.exp_nonneg _)
  -- (4) arithmetic: the exponent is exactly `-α r²/8`
  have hexp : -(lam * s) + 2 * α * lam ^ 2 / (α + β) ^ 2 = -(1 / 8) * α * r ^ 2 := by
    rw [hlamdef, hsdef]
    field_simp
    ring
  refine le_trans hstep1 ?_
  have hreal : (μ.prod μ) {p : ℝ × ℝ | s ≤ p.1 - p.2}
      ≤ ENNReal.ofReal (Real.exp (-(1 / 8) * α * r ^ 2)) := by
    rw [← ofReal_measureReal (μ := μ.prod μ)
      (s := {p : ℝ × ℝ | s ≤ p.1 - p.2})]
    apply ENNReal.ofReal_le_ofReal
    calc (μ.prod μ).real {p : ℝ × ℝ | s ≤ p.1 - p.2}
        ≤ Real.exp (-(lam * s)) * Real.exp (2 * α * lam ^ 2 / (α + β) ^ 2) := hmarkov
      _ = Real.exp (-(1 / 8) * α * r ^ 2) := by rw [← Real.exp_add, hexp]
  calc 2 * (μ.prod μ) {p : ℝ × ℝ | s ≤ p.1 - p.2}
      ≤ 2 * ENNReal.ofReal (Real.exp (-(1 / 8) * α * r ^ 2)) := by gcongr
    _ = ENNReal.ofReal (2 * Real.exp (-(1 / 8) * α * r ^ 2)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
        norm_num

/-- **Unconditional, but trivial half.** Wherever the claimed bound is `≥ 1` — i.e.
`α r² ≤ 8 log 2` — the statement follows from `ν S ≤ ν univ = 1` and needs no analytic input.
Together with the reduction above this pins the un-discharged region to `α r² > 8 log 2`
(hence `α > 8 log 2 ≈ 5.545`, since `r ≤ 1`). -/
theorem betaMeasure_prod_abs_sub_le_of_log2 {α β r : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hx : α * r ^ 2 ≤ 8 * Real.log 2) :
    ((betaMeasure α β).prod (betaMeasure α β))
        {p : ℝ × ℝ | r * (α / (α + β)) ≤ |p.1 - p.2|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(1 / 8) * α * r ^ 2)) := by
  set μ : Measure ℝ := betaMeasure α β with hμdef
  haveI : IsProbabilityMeasure μ := isProbabilityMeasureBeta hα hβ
  have h1 : (μ.prod μ) {p : ℝ × ℝ | r * (α / (α + β)) ≤ |p.1 - p.2|} ≤ 1 :=
    (measure_mono (Set.subset_univ _)).trans (by rw [measure_univ])
  have h2 : (1 : ℝ) ≤ 2 * Real.exp (-(1 / 8) * α * r ^ 2) := by
    have hkey : -(1 / 8 : ℝ) * α * r ^ 2 = -(α * r ^ 2 / 8) := by ring
    rw [hkey]
    have hhalf : (1 : ℝ) / 2 ≤ Real.exp (-(α * r ^ 2 / 8)) := by
      have h : Real.exp (-(Real.log 2)) ≤ Real.exp (-(α * r ^ 2 / 8)) :=
        Real.exp_le_exp.mpr (by linarith)
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
      norm_num at h
      linarith
    linarith
  refine le_trans h1 ?_
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal h2

end

end TSDPP
