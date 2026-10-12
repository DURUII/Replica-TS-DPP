/-
Copyright (c) 2026 TSDPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TSDPP

/-- Integrating an `ℝ≥0∞`-valued function over a null set gives zero. -/
lemma setLIntegral_of_measure_eq_zero {s : Set ℝ} (hs : volume s = 0) (f : ℝ → ℝ≥0∞) :
    ∫⁻ x in s, f x = 0 := by
  rw [Measure.restrict_eq_zero.mpr hs, lintegral_zero_measure]

/-- Translation invariance of the Lebesgue integral on `ℝ`:
`∫ h (y - c) dy = ∫ h y dy`. -/
lemma lintegral_sub_right (c : ℝ) {h : ℝ → ℝ≥0∞} (hmeas : Measurable h) :
    ∫⁻ y, h (y - c) = ∫⁻ y, h y := by
  have h1 : ∫⁻ y, h y ∂Measure.map (fun y : ℝ => y + (-c)) volume = ∫⁻ y, h (y + (-c)) :=
    lintegral_map hmeas (by fun_prop)
  rw [map_add_right_eq_self volume (-c)] at h1
  simpa [sub_eq_add_neg] using h1.symm

/-- Scaling change of variables for the Lebesgue integral on `ℝ`, unrestricted:
`∫ h (c * y) dy = c⁻¹ * ∫ h y dy` for `0 < c`. -/
lemma lintegral_mul_left_of_pos {c : ℝ} (hc : 0 < c) {h : ℝ → ℝ≥0∞} (hmeas : Measurable h) :
    ∫⁻ y, h (c * y) = ENNReal.ofReal c⁻¹ * ∫⁻ y, h y := by
  have h1 : ∫⁻ y, h y ∂Measure.map (fun y : ℝ => c * y) volume = ∫⁻ y, h (c * y) :=
    lintegral_map hmeas (by fun_prop)
  rw [Real.map_volume_mul_left (ne_of_gt hc), lintegral_smul_measure,
    abs_of_pos (inv_pos.mpr hc), smul_eq_mul] at h1
  exact h1.symm

/-- Scaling change of variables for the Lebesgue integral on `ℝ`, restricted to a set:
`∫_s h = c * ∫_{(c*·)⁻¹' s} h (c * y)` for `0 < c`. -/
lemma setLIntegral_mul_left_of_pos {c : ℝ} (hc : 0 < c) (s : Set ℝ) {h : ℝ → ℝ≥0∞}
    (hmeas : Measurable h) :
    ∫⁻ y in s, h y = ENNReal.ofReal c * ∫⁻ y in (fun y : ℝ => c * y) ⁻¹' s, h (c * y) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hemb : MeasurableEmbedding (fun y : ℝ => c * y) := measurableEmbedding_mulLeft₀ hcne
  have hmap : Measure.map (fun y : ℝ => c * y)
        (volume.restrict ((fun y : ℝ => c * y) ⁻¹' s))
      = ENNReal.ofReal c⁻¹ • volume.restrict s := by
    rw [← hemb.restrict_map volume s, Real.map_volume_mul_left hcne, Measure.restrict_smul,
      abs_of_pos (inv_pos.mpr hc)]
  have h2 : ENNReal.ofReal c⁻¹ * ∫⁻ y in s, h y
      = ∫⁻ y in (fun y : ℝ => c * y) ⁻¹' s, h (c * y) := by
    have h3 := lintegral_map (μ := volume.restrict ((fun y : ℝ => c * y) ⁻¹' s))
      (f := h) (g := fun y : ℝ => c * y) hmeas (by fun_prop)
    rw [hmap, lintegral_smul_measure, smul_eq_mul] at h3
    exact h3
  have hcinv : ENNReal.ofReal c * ENNReal.ofReal c⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul (le_of_lt hc), mul_inv_cancel₀ hcne, ENNReal.ofReal_one]
  calc ∫⁻ y in s, h y
      = (ENNReal.ofReal c * ENNReal.ofReal c⁻¹) * ∫⁻ y in s, h y := by rw [hcinv, one_mul]
    _ = ENNReal.ofReal c * (ENNReal.ofReal c⁻¹ * ∫⁻ y in s, h y) := by rw [mul_assoc]
    _ = ENNReal.ofReal c * ∫⁻ y in (fun y : ℝ => c * y) ⁻¹' s, h (c * y) := by rw [h2]

end TSDPP
