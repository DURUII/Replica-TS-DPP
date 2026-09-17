import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TSDPP

lemma setLIntegral_of_measure_eq_zero {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    (hs : μ s = 0) (f : α → ℝ≥0∞) : ∫⁻ x in s, f x ∂μ = 0 := by
  rw [Measure.restrict_eq_zero.mpr hs, lintegral_zero_measure]

lemma lintegral_sub_right (c : ℝ) {h : ℝ → ℝ≥0∞} (hmeas : Measurable h) :
    ∫⁻ y, h (y - c) = ∫⁻ y, h y := by
  have hmap : Measure.map (fun y : ℝ => y - c) volume = volume := by
    have := map_add_right_eq_self (μ := volume) (-c)
    simpa [sub_eq_add_neg] using this
  have h1 := lintegral_map (μ := volume) (f := h) (g := fun y : ℝ => y - c) hmeas (by fun_prop)
  rw [hmap] at h1
  exact h1.symm

lemma lintegral_mul_left_of_pos {c : ℝ} (hc : 0 < c) {h : ℝ → ℝ≥0∞} (hmeas : Measurable h) :
    ∫⁻ y, h (c * y) = ENNReal.ofReal c⁻¹ * ∫⁻ y, h y := by
  have hmap : Measure.map (fun y : ℝ => c * y) volume = ENNReal.ofReal c⁻¹ • volume := by
    rw [Real.map_volume_mul_left hc.ne']
    simp [abs_of_pos (inv_pos.mpr hc)]
  have h1 := lintegral_map (μ := volume) (f := h) (g := fun y : ℝ => c * y) hmeas (by fun_prop)
  rw [hmap, lintegral_smul_measure] at h1
  rw [h1.symm]
  rfl

end TSDPP
