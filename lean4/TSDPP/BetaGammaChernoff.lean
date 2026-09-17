/-
Copyright (c) 2026 TSDPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import TSDPP.GammaMGF

/-!
# The Chernoff step of the one-sample Beta tail bound, in the Gamma picture

If `G ~ Gamma(α,1)` and `H ~ Gamma(β,1)` are independent then `G/(G+H) ~ Beta(α,β)`, so

  `Pr(X ≥ t) = Pr(G(1-t) ≥ Ht) ≤ E[exp (u * (G(1-t) - Ht))]`   for every `u > 0`,

and the exponential *factors* across the product measure, so the expectation is a product of two
Gamma Laplace transforms.  Each factor was already evaluated in `TSDPP.GammaMGF`:

  `∫⁻ x, exp (s * x) ∂(gammaMeasure a 1) = (1 - s) ^ (-a)`   for `s < 1`.

This file proves the resulting identity.  Note what it does **not** need: no confluent
hypergeometric function.  The factorisation is exactly what buys that — the Beta MGF is a `₁F₁`,
but the *product* of a Gamma Laplace transform at a positive argument and one at a negative
argument is elementary.  See `DESIGN.md` GAP-2c.
-/

open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace TSDPP

/-- **The Chernoff step, factored.**  For `α, β > 0` and any real `u, t` satisfying the two
finiteness conditions `u(1-t) < 1` and `-(ut) < 1`,

  `∫⁻ p, exp (u * (p.1 * (1 - t) - p.2 * t)) ∂(gammaMeasure α 1 ⊗ gammaMeasure β 1)
     = (1 - u(1-t))^(-α) * (1 + ut)^(-β)`.

**`u` is not required to be positive**, and this is the point of stating it this way: the *upper*
tail of `X` uses `u > 0`, the *lower* tail uses `u < 0`, and both are the same identity.  The
hypotheses are exactly the two Laplace-transform conditions: `gammaMeasure_lintegral_exp` applies
at `u(1-t)` and at `-ut`, and needs each to be `< 1`.  `u(1-t) < 1` also gives `1 - u(1-t) > 0`,
so the base of the first `rpow` is positive; `-(ut) < 1` likewise gives `1 + ut > 0`. -/
theorem gammaMeasure_prod_lintegral_exp {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    {u t : ℝ} (hu1 : u * (1 - t) < 1) (hu2 : -(u * t) < 1) :
    ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Real.exp (u * (p.1 * (1 - t) - p.2 * t)))
        ∂(gammaMeasure α 1).prod (gammaMeasure β 1)
      = ENNReal.ofReal ((1 - u * (1 - t)) ^ (-α) * (1 + u * t) ^ (-β)) := by
  have hfac : ∀ p : ℝ × ℝ,
      ENNReal.ofReal (Real.exp (u * (p.1 * (1 - t) - p.2 * t)))
        = ENNReal.ofReal (Real.exp ((u * (1 - t)) * p.1))
          * ENNReal.ofReal (Real.exp ((-(u * t)) * p.2)) := by
    intro p
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 1
    ring_nf
  -- `lintegral_prod_mul` needs `SFinite` on both factors, which `IsProbabilityMeasure` supplies.
  -- These are `have`, not `haveI`: the goal is a proposition, so the local instance can be an
  -- ordinary hypothesis (trap: `linter.style.haveILetI`).
  have hprobα : IsProbabilityMeasure (gammaMeasure α 1) := isProbabilityMeasure_gammaMeasure hα one_pos
  have hprobβ : IsProbabilityMeasure (gammaMeasure β 1) := isProbabilityMeasure_gammaMeasure hβ one_pos
  simp only [hfac]
  rw [lintegral_prod_mul (μ := gammaMeasure α 1) (ν := gammaMeasure β 1)
      (f := fun x : ℝ => ENNReal.ofReal (Real.exp ((u * (1 - t)) * x)))
      (g := fun y : ℝ => ENNReal.ofReal (Real.exp ((-(u * t)) * y)))
      (by fun_prop) (by fun_prop)]
  rw [gammaMeasure_lintegral_exp hα hu1, gammaMeasure_lintegral_exp hβ hu2]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ 1 - u * (1 - t)) _)]
  congr 1
  rw [sub_neg_eq_add]

/-- **Markov, on the product measure.**  The event whose probability we want is

  `{p | 0 ≤ u * (p.1 * (1 - t) - p.2 * t)}`,

which is exactly `{p | t ≤ p.1 / (p.1 + p.2)}` read without a division; on it `exp` of the
integrand is `≥ 1`, so `meas_le_lintegral₀` bounds the measure by the integral already evaluated
in `gammaMeasure_prod_lintegral_exp`.

Note the hypotheses: **only** the two Laplace finiteness conditions.  No sign condition on `u` is
needed, because `exp y ≥ 1 ↔ 0 ≤ y` holds either way — the event is *defined* by `0 ≤ u * (…)`,
so for `u < 0` it automatically picks out the complementary half rather than being false.  That is
what lets one statement serve both tails. -/
theorem gammaMeasure_prod_meas_le {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    {u t : ℝ} (hu1 : u * (1 - t) < 1) (hu2 : -(u * t) < 1) :
    ((gammaMeasure α 1).prod (gammaMeasure β 1))
        {p : ℝ × ℝ | 0 ≤ u * (p.1 * (1 - t) - p.2 * t)}
      ≤ ENNReal.ofReal ((1 - u * (1 - t)) ^ (-α) * (1 + u * t) ^ (-β)) := by
  refine (meas_le_lintegral₀ (μ := (gammaMeasure α 1).prod (gammaMeasure β 1))
      (f := fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (u * (p.1 * (1 - t) - p.2 * t))))
      (by fun_prop) fun p hp => ?_).trans (le_of_eq ?_)
  · rw [ENNReal.one_le_ofReal]
    exact Real.one_le_exp hp
  · exact gammaMeasure_prod_lintegral_exp hα hβ hu1 hu2

/-- The Gamma law carries no mass on `(-∞, 0)`.  Mathlib has no support lemma for `gammaMeasure`,
so it is extracted here from the definition: `gammaMeasure a r = volume.withDensity (gammaPDF a r)`
and `gammaPDFReal a r x = 0` for `x < 0`. -/
theorem gammaMeasure_apply_Iio_zero (a r : ℝ) : gammaMeasure a r (Set.Iio 0) = 0 := by
  rw [gammaMeasure, withDensity_apply _ measurableSet_Iio]
  have h0 : ∀ x ∈ Set.Iio (0 : ℝ), gammaPDF a r x = 0 := by
    intro x hx
    simp only [Set.mem_Iio] at hx
    simp only [gammaPDF, gammaPDFReal, ite_eq_right (not_le.mpr hx), ENNReal.ofReal_zero]
  rw [setLIntegral_congr_fun measurableSet_Iio h0]
  simp

/-- **The one-sample Beta tail bound**, in the Gamma picture.

  `Pr (X ≥ t) ≤ (1 - u(1-t))^(-α) * (1 + ut)^(-β)`   for every `u > 0` with `u(1-t) < 1`.

The hypothesis `hmap` is the Beta–Gamma ratio law; everything else is proved here.  The only
delicate point is that the event inclusion

  `{p | t ≤ p.1/(p.1+p.2)} ⊆ {p | 0 ≤ p.1(1-t) - p.2*t}`

holds *off a null set*: it can fail when `p.1 + p.2 < 0`, which the product Gamma measure does not
see (`gammaMeasure_apply_Iio_zero`).  Both `hmap` and this null set are handled here, so the
lemma is stated with the ratio law as its single external input. -/
theorem betaMeasure_Ici_le {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    {u t : ℝ} (hu : 0 < u) (ht : 0 < t) (hu1 : u * (1 - t) < 1)
    (hmap : betaMeasure α β = ((gammaMeasure α 1).prod (gammaMeasure β 1)).map
              (fun p : ℝ × ℝ => p.1 / (p.1 + p.2))) :
    betaMeasure α β (Set.Ici t)
      ≤ ENNReal.ofReal ((1 - u * (1 - t)) ^ (-α) * (1 + u * t) ^ (-β)) := by
  have hprobα : IsProbabilityMeasure (gammaMeasure α 1) := isProbabilityMeasure_gammaMeasure hα one_pos
  have hprobβ : IsProbabilityMeasure (gammaMeasure β 1) := isProbabilityMeasure_gammaMeasure hβ one_pos
  -- The ratio map is measurable, so `map_apply` converts the pushforward to a preimage.
  have hfm : Measurable fun p : ℝ × ℝ => p.1 / (p.1 + p.2) := by fun_prop
  rw [hmap, Measure.map_apply hfm measurableSet_Ici]
  -- The null set on which the two events differ.
  have hN1 : (gammaMeasure α 1) (Set.Iio (0 : ℝ)) = 0 := gammaMeasure_apply_Iio_zero α 1
  have hN2 : (gammaMeasure β 1) (Set.Iio (0 : ℝ)) = 0 := gammaMeasure_apply_Iio_zero β 1
  have hN : ((gammaMeasure α 1).prod (gammaMeasure β 1))
      {p : ℝ × ℝ | p.1 < 0 ∨ p.2 < 0} = 0 := by
    rw [Set.ofPred_or, measure_union_null_iff]
    constructor
    · have hrect : {p : ℝ × ℝ | p.1 < 0} = Set.Iio (0 : ℝ) ×ˢ Set.univ := by
        ext p; simp
      rw [hrect, Measure.prod_prod, hN1, zero_mul]
    · have hrect : {p : ℝ × ℝ | p.2 < 0} = Set.univ ×ˢ Set.Iio (0 : ℝ) := by
        ext p; simp
      rw [hrect, Measure.prod_prod, hN2, mul_zero]
  -- The event inclusion, off that null set.
  have hsub : (fun p : ℝ × ℝ => p.1 / (p.1 + p.2)) ⁻¹' Set.Ici t
      ⊆ {p : ℝ × ℝ | 0 ≤ u * (p.1 * (1 - t) - p.2 * t)} ∪ {p : ℝ × ℝ | p.1 < 0 ∨ p.2 < 0} := by
    intro p hp
    by_cases hbad : p.1 < 0 ∨ p.2 < 0
    · exact Or.inr hbad
    · refine Or.inl ?_
      push Not at hbad
      obtain ⟨h1, h2⟩ := hbad
      have hpos : 0 < p.1 + p.2 := by
        rcases eq_or_lt_of_le h1 with h | h
        · rcases eq_or_lt_of_le h2 with h' | h'
          · exfalso
            simp only [Set.mem_preimage, Set.mem_Ici, ← h, ← h', add_zero, div_zero] at hp
            exact absurd hp (not_le.mpr ht)
          · linarith
        · linarith
      simp only [Set.mem_preimage, Set.mem_Ici] at hp
      rw [le_div_iff₀ hpos] at hp
      refine mul_nonneg hu.le ?_
      nlinarith [hp]
  calc ((gammaMeasure α 1).prod (gammaMeasure β 1))
        ((fun p : ℝ × ℝ => p.1 / (p.1 + p.2)) ⁻¹' Set.Ici t)
      ≤ ((gammaMeasure α 1).prod (gammaMeasure β 1))
          ({p : ℝ × ℝ | 0 ≤ u * (p.1 * (1 - t) - p.2 * t)}
            ∪ {p : ℝ × ℝ | p.1 < 0 ∨ p.2 < 0}) := measure_mono hsub
    _ ≤ ((gammaMeasure α 1).prod (gammaMeasure β 1))
          {p : ℝ × ℝ | 0 ≤ u * (p.1 * (1 - t) - p.2 * t)}
        + ((gammaMeasure α 1).prod (gammaMeasure β 1))
          {p : ℝ × ℝ | p.1 < 0 ∨ p.2 < 0} := measure_union_le _ _
    _ = ((gammaMeasure α 1).prod (gammaMeasure β 1))
          {p : ℝ × ℝ | 0 ≤ u * (p.1 * (1 - t) - p.2 * t)} + 0 := by rw [hN]
    _ = ((gammaMeasure α 1).prod (gammaMeasure β 1))
          {p : ℝ × ℝ | 0 ≤ u * (p.1 * (1 - t) - p.2 * t)} := add_zero _
    _ ≤ ENNReal.ofReal ((1 - u * (1 - t)) ^ (-α) * (1 + u * t) ^ (-β)) :=
        gammaMeasure_prod_meas_le hα hβ hu1 (by nlinarith [hu, ht])

/-- **The one-sample Beta *lower* tail bound** — the twin of `betaMeasure_Ici_le`.

  `Pr (X ≤ t) ≤ (1 + v(1-t))^(-α) * (1 - vt)^(-β)`   for every `v > 0` with `vt < 1`.

This is not a second Chernoff argument: it is `gammaMeasure_prod_lintegral_exp` at `u := -v`,
where the integrand's exponent flips sign and the event `{G(1-t) - Ht ≤ 0}` becomes
`{u * (G(1-t) - Ht) ≥ 0}`.  That the same identity serves both tails is exactly why `u` was not
required to be positive above. -/
theorem betaMeasure_Iio_le {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    {v t : ℝ} (hv : 0 < v) (ht1 : t < 1) (hvt : v * t < 1)
    (hmap : betaMeasure α β = ((gammaMeasure α 1).prod (gammaMeasure β 1)).map
              (fun p : ℝ × ℝ => p.1 / (p.1 + p.2))) :
    betaMeasure α β (Set.Iio t)
      ≤ ENNReal.ofReal ((1 + v * (1 - t)) ^ (-α) * (1 - v * t) ^ (-β)) := by
  have hprobα : IsProbabilityMeasure (gammaMeasure α 1) := isProbabilityMeasure_gammaMeasure hα one_pos
  have hprobβ : IsProbabilityMeasure (gammaMeasure β 1) := isProbabilityMeasure_gammaMeasure hβ one_pos
  have hfm : Measurable fun p : ℝ × ℝ => p.1 / (p.1 + p.2) := by fun_prop
  have h1mt : (0 : ℝ) < 1 - t := sub_pos.mpr ht1
  have hu1 : (-v) * (1 - t) < 1 := by nlinarith [hv, h1mt]
  have hu2 : -((-v) * t) < 1 := by nlinarith [hvt]
  have hN1 : (gammaMeasure α 1) (Set.Iio (0 : ℝ)) = 0 := gammaMeasure_apply_Iio_zero α 1
  have hN2 : (gammaMeasure β 1) (Set.Iio (0 : ℝ)) = 0 := gammaMeasure_apply_Iio_zero β 1
  have hN : ((gammaMeasure α 1).prod (gammaMeasure β 1))
      {p : ℝ × ℝ | p.1 < 0 ∨ p.2 < 0} = 0 := by
    rw [Set.ofPred_or, measure_union_null_iff]
    constructor
    · have hrect : {p : ℝ × ℝ | p.1 < 0} = Set.Iio (0 : ℝ) ×ˢ Set.univ := by ext p; simp
      rw [hrect, Measure.prod_prod, hN1, zero_mul]
    · have hrect : {p : ℝ × ℝ | p.2 < 0} = Set.univ ×ˢ Set.Iio (0 : ℝ) := by ext p; simp
      rw [hrect, Measure.prod_prod, hN2, mul_zero]
  rw [hmap, Measure.map_apply hfm measurableSet_Iio]
  -- `X ≤ t` iff `G(1-t) ≤ Ht`, i.e. `(-v) * (G(1-t) - Ht) ≥ 0`, off the null set.
  have hsub : (fun p : ℝ × ℝ => p.1 / (p.1 + p.2)) ⁻¹' Set.Iio t
      ⊆ {p : ℝ × ℝ | 0 ≤ (-v) * (p.1 * (1 - t) - p.2 * t)} ∪ {p : ℝ × ℝ | p.1 < 0 ∨ p.2 < 0} := by
    intro p hp
    by_cases hbad : p.1 < 0 ∨ p.2 < 0
    · exact Or.inr hbad
    · refine Or.inl ?_
      push Not at hbad
      obtain ⟨h1, h2⟩ := hbad
      -- Both coordinates are `≥ 0` here.  The degenerate point `(0,0)` has to be split off
      -- rather than refuted: `0/0 = 0 < t` is *true* when `t > 0`, so it lands in the preimage
      -- legitimately — it just forces `p.1 + p.2 = 0`, where the division rewrite is invalid.
      rcases lt_or_eq_of_le (by linarith : (0:ℝ) ≤ p.1 + p.2) with hpos | hzero
      · simp only [Set.mem_preimage, Set.mem_Iio] at hp
        rw [div_lt_iff₀ hpos] at hp
        refine mul_nonneg_of_nonpos_of_nonpos (by linarith : (-v) ≤ 0) ?_
        nlinarith [hp]
      · have h1' : p.1 = 0 := by linarith
        have h2' : p.2 = 0 := by linarith
        simp [h1', h2']
  calc ((gammaMeasure α 1).prod (gammaMeasure β 1))
        ((fun p : ℝ × ℝ => p.1 / (p.1 + p.2)) ⁻¹' Set.Iio t)
      ≤ ((gammaMeasure α 1).prod (gammaMeasure β 1))
          ({p : ℝ × ℝ | 0 ≤ (-v) * (p.1 * (1 - t) - p.2 * t)}
            ∪ {p : ℝ × ℝ | p.1 < 0 ∨ p.2 < 0}) := measure_mono hsub
    _ ≤ ((gammaMeasure α 1).prod (gammaMeasure β 1))
          {p : ℝ × ℝ | 0 ≤ (-v) * (p.1 * (1 - t) - p.2 * t)}
        + ((gammaMeasure α 1).prod (gammaMeasure β 1))
          {p : ℝ × ℝ | p.1 < 0 ∨ p.2 < 0} := measure_union_le _ _
    _ = ((gammaMeasure α 1).prod (gammaMeasure β 1))
          {p : ℝ × ℝ | 0 ≤ (-v) * (p.1 * (1 - t) - p.2 * t)} + 0 := by rw [hN]
    _ = ((gammaMeasure α 1).prod (gammaMeasure β 1))
          {p : ℝ × ℝ | 0 ≤ (-v) * (p.1 * (1 - t) - p.2 * t)} := add_zero _
    _ ≤ ENNReal.ofReal ((1 + v * (1 - t)) ^ (-α) * (1 - v * t) ^ (-β)) := by
        have h := gammaMeasure_prod_meas_le (α := α) (β := β) hα hβ
          (u := -v) (t := t) hu1 hu2
        rwa [show (1 - (-v) * (1 - t)) = 1 + v * (1 - t) by ring,
             show (1 + (-v) * t) = 1 - v * t by ring] at h

end TSDPP
