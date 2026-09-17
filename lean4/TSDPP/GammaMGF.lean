/-
Copyright (c) 2026 TSDPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Measurability of the Gamma density, the Gamma MGF, and the Gamma cdf

This file collects three self-contained measure-theoretic facts about the Gamma distribution on
`ℝ` as formalised in `Mathlib/Probability/Distributions/Gamma.lean`.

* `TSDPP.measurable_gammaPDF`: the `ℝ≥0∞`-valued Gamma density is measurable.
* `TSDPP.gammaMeasure_lintegral_exp`: the Laplace transform (moment generating function) of
  `gammaMeasure a 1` at a real parameter `t < 1` equals `(1 - t) ^ (-a)`.
* `TSDPP.cdf_gammaMeasure_eq_setLIntegral`: the cdf of `gammaMeasure a r` is the
  set-Lebesgue-integral of the density over `Set.Iic x`.

## Main results

* `TSDPP.measurable_gammaPDF`
* `TSDPP.gammaMeasure_lintegral_exp`
* `TSDPP.cdf_gammaMeasure_eq_setLIntegral`
-/

open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace TSDPP

/-- The `ℝ≥0∞`-valued Gamma density `gammaPDF a r` is measurable.

By definition `gammaPDF a r = ENNReal.ofReal ∘ gammaPDFReal a r`, and `gammaPDFReal a r` is
measurable (`ProbabilityTheory.measurable_gammaPDFReal`); `ENNReal.ofReal` preserves
measurability (`Measurable.ennreal_ofReal`). -/
theorem measurable_gammaPDF (a r : ℝ) : Measurable (gammaPDF a r) :=
  (measurable_gammaPDFReal a r).ennreal_ofReal

/-- **The moment generating function of the Gamma distribution.**

For `a > 0` and a real parameter `t < 1`,

  `∫⁻ x, exp (t * x) ∂(gammaMeasure a 1) = (1 - t) ^ (-a)`.

Note that `gammaMeasure a 1` is the Gamma law with shape `a` and rate `1`, so the Laplace
transform is finite exactly on `t < 1` (`1` being the rate). The proof rewrites the `ℝ≥0∞`
integral against `gammaMeasure a 1 = volume.withDensity (gammaPDF a 1)` as a Lebesgue integral of
`gammaPDFReal a 1 x * exp (t * x)`, which vanishes on `(-∞, 0]` and equals
`1 ^ a / Gamma a * x ^ (a - 1) * exp (-((1 - t) * x))` on `Ioi 0`; the Gamma integral
`Real.integral_rpow_mul_exp_neg_mul_Ioi` then evaluates it to
`1 / Gamma a * ((1 / (1 - t)) ^ a * Gamma a) = (1 - t) ^ (-a)`.

The parameter is called `t` rather than `λ` because `λ` is a reserved token in Lean 4 and cannot
be used as a binder name. -/
theorem gammaMeasure_lintegral_exp {a : ℝ} (ha : 0 < a) {t : ℝ} (ht : t < 1) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (t * x)) ∂(gammaMeasure a 1)
      = ENNReal.ofReal ((1 - t) ^ (-a)) := by
  have hgm : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (t * x)) := by fun_prop
  -- Step 1: the pointwise identification `gammaPDF a 1 x * ofReal (exp (t * x)) = ofReal (g x)`.
  have hg : ∀ x : ℝ, gammaPDF a 1 x * ENNReal.ofReal (Real.exp (t * x))
      = ENNReal.ofReal (gammaPDFReal a 1 x * Real.exp (t * x)) := by
    intro x
    change ENNReal.ofReal (gammaPDFReal a 1 x) * ENNReal.ofReal (Real.exp (t * x))
        = ENNReal.ofReal (gammaPDFReal a 1 x * Real.exp (t * x))
    rw [← ENNReal.ofReal_mul (gammaPDFReal_nonneg ha one_pos x)]
  -- Step 2: the integrand is almost everywhere nonnegative.
  have hnn : 0 ≤ᵐ[volume] fun x : ℝ => gammaPDFReal a 1 x * Real.exp (t * x) :=
    Filter.Eventually.of_forall fun x =>
      mul_nonneg (gammaPDFReal_nonneg ha one_pos x) (Real.exp_pos _).le
  -- Step 3: the integrand is Lebesgue integrable.
  have hint : Integrable (fun x : ℝ => gammaPDFReal a 1 x * Real.exp (t * x)) volume := by
    have h1 : IntegrableOn (fun x : ℝ => x ^ (a - 1) * Real.exp (-((1 - t) * x)))
        (Set.Ioi 0) := by
      have h : IntegrableOn (fun x : ℝ => x ^ (a - 1) * Real.exp (-(1 - t) * x))
          (Set.Ioi 0) := by
        simpa only [Real.rpow_one] using
          (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a - 1) (b := 1 - t)
            (by linarith) one_pos (by linarith))
      refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
      change x ^ (a - 1) * Real.exp (-(1 - t) * x) = x ^ (a - 1) * Real.exp (-((1 - t) * x))
      rw [show -(1 - t) * x = -((1 - t) * x) by ring]
    have h2 : IntegrableOn
        (fun x : ℝ => 1 ^ a / Real.Gamma a * (x ^ (a - 1) * Real.exp (-((1 - t) * x))))
        (Set.Ioi 0) :=
      h1.const_mul _
    have h3 : IntegrableOn (fun x : ℝ => gammaPDFReal a 1 x * Real.exp (t * x))
        (Set.Ioi 0) := by
      refine h2.congr_fun (fun x hx => ?_) measurableSet_Ioi
      have hx' : (0 : ℝ) < x := hx
      simp only [gammaPDFReal, ite_eq_left hx'.le]
      rw [show -((1 - t) * x) = -(1 * x) + t * x by ring, Real.exp_add]
      ring
    have h4 : IntegrableOn (fun x : ℝ => gammaPDFReal a 1 x * Real.exp (t * x))
        (Set.Ici 0) :=
      (integrableOn_Ici_iff_integrableOn_Ioi
        (f := fun x : ℝ => gammaPDFReal a 1 x * Real.exp (t * x)) (b := 0)).mpr h3
    refine h4.integrable_of_forall_notMem_eq_zero (fun x hx => ?_)
    simp only [Set.mem_Ici, not_le] at hx
    rw [gammaPDFReal, ite_eq_right (not_le.mpr hx), zero_mul]
  -- Step 4: the value of the Lebesgue integral.
  have hval : ∫ x, gammaPDFReal a 1 x * Real.exp (t * x) = (1 - t) ^ (-a) := by
    have hpt : Set.EqOn (fun x : ℝ => gammaPDFReal a 1 x * Real.exp (t * x))
        (fun x : ℝ => 1 ^ a / Real.Gamma a * (x ^ (a - 1) * Real.exp (-((1 - t) * x))))
        (Set.Ioi 0) := by
      intro x hx
      have hx' : (0 : ℝ) < x := hx
      simp only [gammaPDFReal, ite_eq_left hx'.le]
      rw [show -((1 - t) * x) = -(1 * x) + t * x by ring, Real.exp_add]
      ring
    have hsupp : ∫ x, gammaPDFReal a 1 x * Real.exp (t * x)
        = ∫ x in Set.Ici 0, gammaPDFReal a 1 x * Real.exp (t * x) := by
      have hzero : ∀ x, x ∉ Set.Ici 0 → gammaPDFReal a 1 x * Real.exp (t * x) = 0 := by
        intro x hx
        simp only [Set.mem_Ici, not_le] at hx
        rw [gammaPDFReal, ite_eq_right (not_le.mpr hx), zero_mul]
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    rw [hsupp, integral_Ici_eq_integral_Ioi,
      setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
      Real.integral_rpow_mul_exp_neg_mul_Ioi ha (by linarith : (0 : ℝ) < 1 - t)]
    rw [Real.one_rpow]
    have hG : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
    rw [mul_comm ((1 / (1 - t)) ^ a) (Real.Gamma a), ← mul_assoc, one_div,
      inv_mul_cancel₀ hG, one_mul]
    rw [one_div, Real.inv_rpow (by linarith : (0 : ℝ) ≤ 1 - t),
      Real.rpow_neg (by linarith : (0 : ℝ) ≤ 1 - t)]
  -- Step 5: assemble.
  rw [gammaMeasure,
    lintegral_withDensity_eq_lintegral_mul (f := gammaPDF a 1) volume
      (measurable_gammaPDF a 1) hgm]
  rw [show (fun x => (gammaPDF a 1 * fun x => ENNReal.ofReal (Real.exp (t * x))) x)
      = fun x => ENNReal.ofReal (gammaPDFReal a 1 x * Real.exp (t * x)) from funext hg]
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, hval]

/-- The cdf of the Gamma measure `gammaMeasure a r` is the set-Lebesgue-integral of the density
`gammaPDF a r` over `Set.Iic x`, i.e. `cdf μ x = μ (Iic x)` for `μ = gammaMeasure a r`.

Two remarks on the shape of this statement.

* `ProbabilityTheory.cdf μ x` is a *real* number while `∫⁻ y in Iic x, gammaPDF a r y` is an
  `ℝ≥0∞`; the coercion `ℝ → ℝ≥0∞` is `ENNReal.ofReal`, so the statement carries an explicit
  `ENNReal.ofReal` on the left. Equivalently, by `ENNReal.ofReal_toReal`, one may state it as
  `cdf (gammaMeasure a r) x = (∫⁻ y in Iic x, gammaPDF a r y).toReal`.
* The hypotheses `0 < a` and `0 < r` are needed: `cdf` is *normalised* (its
  `ProbabilityTheory.tendsto_cdf_atTop` limit is `1` for *every* measure), so `cdf μ` agrees with
  `μ (Iic ·)` only when `μ` is a probability measure. For the Gamma family this holds exactly
  when `0 < a` and `0 < r` (`ProbabilityTheory.isProbabilityMeasure_gammaMeasure`). -/
theorem cdf_gammaMeasure_eq_setLIntegral {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (x : ℝ) :
    ENNReal.ofReal (cdf (gammaMeasure a r) x) = ∫⁻ y in Set.Iic x, gammaPDF a r y := by
  have hprob : IsProbabilityMeasure (gammaMeasure a r) := isProbabilityMeasure_gammaMeasure ha hr
  rw [ofReal_cdf (gammaMeasure a r) x, gammaMeasure, withDensity_apply _ measurableSet_Iic]

end TSDPP
