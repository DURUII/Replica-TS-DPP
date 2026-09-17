import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Scratch

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

end Scratch
