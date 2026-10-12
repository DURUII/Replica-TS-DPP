/-
Copyright (c) 2026 TSDPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Set

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
    rw [Real.map_volume_mul_left (ne_of_gt hc)]
    simp [abs_of_pos (inv_pos.mpr hc)]
  have h1 := lintegral_map (μ := volume) (f := h) (g := fun y : ℝ => c * y) hmeas (by fun_prop)
  rw [hmap, lintegral_smul_measure, smul_eq_mul] at h1
  exact h1.symm

example {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht0 : 0 < t) (ht1 : t < 1) :
    ∫⁻ y, ∫⁻ x, ({p : ℝ × ℝ | t * p.2 ≤ (1 - t) * p.1}.indicator
        (fun p : ℝ × ℝ => gammaPDF a 1 p.1 * gammaPDF b 1 p.2) (x, y)) ∂volume ∂volume
      = ∫⁻ y, ∫⁻ u, (if y ≤ (1 - t) * u then
          gammaPDF a 1 (u - y) * gammaPDF b 1 y else 0) ∂volume ∂volume := by
  refine lintegral_congr fun y => ?_
  have hA : MeasurableSet {p : ℝ × ℝ | t * p.2 ≤ (1 - t) * p.1} :=
    measurableSet_le (measurable_const.mul measurable_snd) (measurable_const.mul measurable_fst)
  have hFm : Measurable (fun p : ℝ × ℝ => gammaPDF a 1 p.1 * gammaPDF b 1 p.2) :=
    ((measurable_gammaPDFReal a 1).ennreal_ofReal.comp measurable_fst).mul
      ((measurable_gammaPDFReal b 1).ennreal_ofReal.comp measurable_snd)
  have hm : Measurable (fun x : ℝ => ({p : ℝ × ℝ | t * p.2 ≤ (1 - t) * p.1}.indicator
        (fun p : ℝ × ℝ => gammaPDF a 1 p.1 * gammaPDF b 1 p.2) (x, y))) :=
    (hFm.indicator hA).comp (measurable_prodMk_right (y := y))
  rw [(lintegral_sub_right y hm).symm]
  refine lintegral_congr fun u => ?_
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  by_cases h : y ≤ (1 - t) * u
  · rw [ite_eq_left h, ite_eq_left (show t * y ≤ (1 - t) * (u - y) by linarith)]
  · rw [ite_eq_right h, ite_eq_right (show ¬ (t * y ≤ (1 - t) * (u - y)) by linarith)]

end TSDPP
