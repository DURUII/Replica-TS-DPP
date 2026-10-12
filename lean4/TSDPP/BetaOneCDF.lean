/-
Copyright (c) 2026 TSDPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The Beta(1, B) tail, in closed form.

This is the analytic input the Lemma 5 refutation rests on.  It is elementary *because* the first
shape parameter is exactly `1`: then `x ^ (α - 1) = x ^ 0 = 1` and `beta 1 B = Γ(1)Γ(B)/Γ(1+B) = 1/B`,
so the density collapses to the single power `B * (1 - x) ^ (B - 1)` and

    betaMeasure 1 B (Ioo a b) = (1 - a) ^ B - (1 - b) ^ B

is the integral of a *polynomial* — no Beta CDF, no incomplete Beta function, no `Real.rpow` beyond
the `Nat`-exponent bridge.  Mathlib has no Beta CDF lemma at all (`Distributions/Beta.lean` ends at
`isProbabilityMeasureBeta`), so this is the whole reason the refutation's witness was chosen with
`α = 1`; see `Lemma5Refutation.lean` for the witness and `../DESIGN.md` J-12 for the choice.

The three public theorems carry their hypotheses exactly, and they are not decoration:

* `betaMeasure_one_Ioo` needs `0 ≤ a ≤ b ≤ 1` — outside `[0,1]` the density is zero but `(1-a)^B`
  keeps growing, so the formula is simply false.
* `betaMeasure_one_Ici` needs `t ≤ 1` in addition to `0 ≤ t`.  For `t > 1` the left side is `0`
  while `(1 - t) ^ B` is positive for even `B` and negative for odd `B` — no single formula holds.
  An earlier brief for this file asked for the `Ici` form with only `0 ≤ t`; that statement is
  false, and the extra hypothesis is the fix, not a convenience.
* `betaMeasure_one_Iic` needs both `0 ≤ u` and `u ≤ 1`, for the two matching reasons.
-/
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TSDPP

/-- `beta 1 (B:ℝ) = 1 / B` in reciprocal form. -/
private lemma beta_one_inv (B : ℕ) (hB : 1 ≤ B) : (1 : ℝ) / beta 1 (B : ℝ) = (B : ℝ) := by
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hB)
  have hBne : (B : ℝ) ≠ 0 := ne_of_gt hBpos
  have hGam : Real.Gamma ((B : ℝ) + 1) = (B : ℝ) * Real.Gamma (B : ℝ) := Real.Gamma_add_one hBne
  rw [beta]
  rw [Real.Gamma_one, one_mul]
  rw [show (1 : ℝ) + (B : ℝ) = (B : ℝ) + 1 by ring]
  rw [hGam]
  field_simp [hBne, (Real.Gamma_pos_of_pos hBpos).ne']

/-- `betaMeasure 1 B` is absolutely continuous with respect to Lebesgue measure. -/
private lemma betaMeasure_absolutelyContinuous (B : ℕ) :
    betaMeasure 1 (B : ℝ) ≪ volume := by
  rw [betaMeasure]
  exact withDensity_absolutelyContinuous (volume : Measure ℝ) (betaPDF 1 (B : ℝ))

/-- Lift a Lebesgue `ae_eq` of sets to a `betaMeasure` `ae_eq`. -/
private lemma betaMeasure_ae_eq (B : ℕ) {s t : Set ℝ} (h : s =ᵐ[volume] t) :
    s =ᵐ[betaMeasure 1 (B : ℝ)] t := by
  rw [ae_eq_set] at h ⊢
  exact ⟨betaMeasure_absolutelyContinuous B h.1, betaMeasure_absolutelyContinuous B h.2⟩

/-- For a density measure, `Icc a b` and `Ioo a b` carry the same mass. -/
private lemma betaMeasure_one_Icc_eq_Ioo (B : ℕ) {a b : ℝ} :
    betaMeasure 1 (B : ℝ) (Set.Icc a b) = betaMeasure 1 (B : ℝ) (Set.Ioo a b) := by
  exact (measure_congr (betaMeasure_ae_eq B (Ioo_ae_eq_Icc (μ := volume)))).symm

/-- For a density measure, `Ico a b` and `Ioo a b` carry the same mass. -/
private lemma betaMeasure_one_Ico_eq_Ioo (B : ℕ) {a b : ℝ} :
    betaMeasure 1 (B : ℝ) (Set.Ico a b) = betaMeasure 1 (B : ℝ) (Set.Ioo a b) := by
  exact (measure_congr (betaMeasure_ae_eq B (Ioo_ae_eq_Ico (μ := volume)))).symm

/-- For `B ≥ 1` and `0 ≤ a ≤ b ≤ 1`. -/
theorem betaMeasure_one_Ioo (B : ℕ) (hB : 1 ≤ B) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    betaMeasure 1 (B : ℝ) (Set.Ioo a b)
      = ENNReal.ofReal ((1 - a) ^ B - (1 - b) ^ B) := by
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hB)
  have hBne : (B : ℝ) ≠ 0 := ne_of_gt hBpos
  rw [betaMeasure, withDensity_apply _ measurableSet_Ioo]
  -- ∫⁻ x in Ioo a b, betaPDF 1 (B:ℝ) x = ofReal ((1-a)^B - (1-b)^B)
  have hdensity : ∀ x ∈ Set.Ioo a b,
      betaPDF 1 (B : ℝ) x = ENNReal.ofReal ((B : ℝ) * (1 - x) ^ (B - 1)) := by
    intro x hx
    have hxpos : 0 < x := by
      have : a < x := (Set.mem_Ioo.mp hx).1
      linarith
    have hxlt : x < 1 := by
      have : x < b := (Set.mem_Ioo.mp hx).2
      linarith
    rw [betaPDF_of_pos_lt_one hxpos hxlt]
    have hBsub : (B : ℝ) - 1 = ((B - 1 : ℕ) : ℝ) := by norm_num [Nat.cast_sub hB]
    have hreal : (1 / beta 1 (B : ℝ)) * x ^ ((1 : ℝ) - 1) * (1 - x) ^ ((B : ℝ) - 1)
        = (B : ℝ) * (1 - x) ^ (B - 1) := by
      rw [show (1 : ℝ) - 1 = 0 by norm_num, Real.rpow_zero, hBsub, Real.rpow_natCast]
      rw [beta_one_inv B hB, mul_one]
    rw [hreal]
  rw [setLIntegral_congr_fun measurableSet_Ioo hdensity]
  -- ∫⁻ x in Ioo a b, ofReal (B*(1-x)^(B-1)) = ofReal ((1-a)^B - (1-b)^B)
  rw [setLIntegral_congr (Ioo_ae_eq_Ioc (μ := volume) (a := a) (b := b))]
  -- ∫⁻ x in Ioc a b, ofReal (B*(1-x)^(B-1)) = ofReal ((1-a)^B - (1-b)^B)
  have hInt : ∫ x in Set.Ioc a b, (B : ℝ) * (1 - x) ^ (B - 1) = (1 - a) ^ B - (1 - b) ^ B := by
    rw [← intervalIntegral.integral_of_le hab]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_comp_sub_left (f := fun t => t ^ (B - 1)) (d := 1)]
    rw [integral_pow]
    rw [Nat.sub_add_cancel hB]
    have hden : ((B - 1 : ℕ) : ℝ) + 1 = (B : ℝ) := by norm_num [Nat.cast_sub hB]
    rw [hden]
    field_simp [hBne]
  have hf_cont : Continuous (fun x => (B : ℝ) * (1 - x) ^ (B - 1)) := by fun_prop
  have hfi : Integrable (fun x => (B : ℝ) * (1 - x) ^ (B - 1)) (volume.restrict (Set.Ioc a b)) :=
    hf_cont.integrableOn_Ioc
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc a b)] fun x => (B : ℝ) * (1 - x) ^ (B - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hxle : x ≤ 1 := by
      have : x ≤ b := (Set.mem_Ioc.mp hx).2
      linarith
    exact mul_nonneg (le_of_lt hBpos) (pow_nonneg (sub_nonneg.mpr hxle) (B - 1))
  rw [← ofReal_integral_eq_lintegral_ofReal (f := fun x => (B : ℝ) * (1 - x) ^ (B - 1))
    (μ := volume.restrict (Set.Ioc a b)) hfi hnn]
  rw [hInt]

/-- `Pr(X ≥ t)` for `X ~ Beta(1, B)`, with `0 ≤ t ≤ 1`. -/
theorem betaMeasure_one_Ici (B : ℕ) (hB : 1 ≤ B) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    betaMeasure 1 (B : ℝ) (Set.Ici t) = ENNReal.ofReal ((1 - t) ^ B) := by
  have hIci1 : betaMeasure 1 (B : ℝ) (Set.Ici 1) = 0 := by
    rw [betaMeasure, withDensity_apply _ measurableSet_Ici]
    exact setLIntegral_eq_zero measurableSet_Ici (fun x hx => betaPDF_eq_zero_of_one_le hx)
  have hdisj : Disjoint (Set.Ico t 1) (Set.Ici (1 : ℝ)) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    rw [Set.mem_Ico] at hx1
    rw [Set.mem_Ici] at hx2
    linarith
  calc
    betaMeasure 1 (B : ℝ) (Set.Ici t)
        = betaMeasure 1 (B : ℝ) (Set.Ico t 1 ∪ Set.Ici (1 : ℝ)) := by
          rw [← Set.Ico_union_Ici_eq_Ici ht1]
    _ = betaMeasure 1 (B : ℝ) (Set.Ico t 1) + betaMeasure 1 (B : ℝ) (Set.Ici (1 : ℝ)) := by
          rw [measure_union hdisj measurableSet_Ici]
    _ = betaMeasure 1 (B : ℝ) (Set.Ico t 1) := by simp [hIci1]
    _ = betaMeasure 1 (B : ℝ) (Set.Ioo t 1) := betaMeasure_one_Ico_eq_Ioo B
    _ = ENNReal.ofReal ((1 - t) ^ B - (1 - 1) ^ B) :=
          betaMeasure_one_Ioo B hB ht ht1 le_rfl
    _ = ENNReal.ofReal ((1 - t) ^ B) := by
          rw [sub_self, zero_pow (show B ≠ 0 by omega), sub_zero]

/-- `Pr(X ≤ u)` for `X ~ Beta(1, B)`, with `0 ≤ u ≤ 1`. -/
theorem betaMeasure_one_Iic (B : ℕ) (hB : 1 ≤ B) {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    betaMeasure 1 (B : ℝ) (Set.Iic u) = ENNReal.ofReal (1 - (1 - u) ^ B) := by
  have hIio0 : betaMeasure 1 (B : ℝ) (Set.Iio (0 : ℝ)) = 0 := by
    rw [betaMeasure, withDensity_apply _ measurableSet_Iio]
    exact setLIntegral_eq_zero measurableSet_Iio (fun x hx => betaPDF_eq_zero_of_nonpos (le_of_lt hx))
  have hdisj : Disjoint (Set.Iio (0 : ℝ)) (Set.Icc 0 u) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    rw [Set.mem_Iio] at hx1
    rw [Set.mem_Icc] at hx2
    linarith
  calc
    betaMeasure 1 (B : ℝ) (Set.Iic u)
        = betaMeasure 1 (B : ℝ) (Set.Iio (0 : ℝ) ∪ Set.Icc 0 u) := by
          rw [← Set.Iio_union_Icc_eq_Iic hu]
    _ = betaMeasure 1 (B : ℝ) (Set.Iio (0 : ℝ)) + betaMeasure 1 (B : ℝ) (Set.Icc 0 u) := by
          rw [measure_union hdisj measurableSet_Icc]
    _ = betaMeasure 1 (B : ℝ) (Set.Icc 0 u) := by simp [hIio0]
    _ = betaMeasure 1 (B : ℝ) (Set.Ioo 0 u) := betaMeasure_one_Icc_eq_Ioo B
    _ = ENNReal.ofReal ((1 - 0) ^ B - (1 - u) ^ B) :=
          betaMeasure_one_Ioo B hB (le_refl 0) hu hu1
    _ = ENNReal.ofReal (1 - (1 - u) ^ B) := by
          rw [sub_zero, one_pow]

end TSDPP
