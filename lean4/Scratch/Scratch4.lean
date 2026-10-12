/-
Copyright (c) 2026 TSDPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Set

namespace TSDPP

lemma setLIntegral_of_measure_eq_zero {s : Set ℝ} (hs : volume s = 0) (f : ℝ → ℝ≥0∞) :
    ∫⁻ x in s, f x = 0 := by
  rw [Measure.restrict_eq_zero.mpr hs, lintegral_zero_measure]

/-- Reflection: `r ↦ 1 - r` preserves Lebesgue measure. -/
lemma lintegral_one_sub {f : ℝ → ℝ≥0∞} (hmeas : Measurable f) :
    ∫⁻ r, f (1 - r) = ∫⁻ r, f r := by
  have hmap : Measure.map (fun r : ℝ => 1 - r) volume = volume := by
    have hcomp : (fun r : ℝ => 1 - r) = (fun u : ℝ => 1 + u) ∘ (fun r : ℝ => -r) := rfl
    rw [hcomp, ← Measure.map_map (g := fun u : ℝ => 1 + u) (f := fun r : ℝ => -r)
      (by fun_prop) (by fun_prop)]
    rw [Measure.map_neg_eq_self (volume : Measure ℝ), map_add_left_eq_self]
  have h1 := lintegral_map (μ := volume) (f := f) (g := fun r : ℝ => 1 - r) hmeas
    (by fun_prop)
  rw [hmap] at h1
  exact h1.symm

/-- The set version of reflection. -/
lemma setLIntegral_one_sub (s : Set ℝ) (hs : MeasurableSet s) {f : ℝ → ℝ≥0∞}
    (hmeas : Measurable f) :
    ∫⁻ r in s, f r = ∫⁻ w in (fun r : ℝ => 1 - r) ⁻¹' s, f (1 - w) := by
  have h : ∫⁻ r, s.indicator f (1 - r) = ∫⁻ r in s, f r := by
    rw [lintegral_one_sub (hmeas.indicator hs), lintegral_indicator hs]
  have h2 : ∫⁻ r, s.indicator f (1 - r)
      = ∫⁻ w in (fun r : ℝ => 1 - r) ⁻¹' s, f (1 - w) := by
    rw [← lintegral_indicator (hs.preimage (by fun_prop)) (fun w => f (1 - w))]
    refine lintegral_congr fun w => ?_
    by_cases hw : (1 - w) ∈ s
    · rw [Set.indicator_of_mem hw,
        Set.indicator_of_mem (show w ∈ (fun r : ℝ => 1 - r) ⁻¹' s from hw)]
    · rw [Set.indicator_of_notMem hw,
        Set.indicator_of_notMem (show w ∉ (fun r : ℝ => 1 - r) ⁻¹' s from hw)]
  exact h.symm.trans h2

/-- Two sets that differ only in a single point have the same set integral. -/
lemma setLIntegral_congr_of_diff_subset_singleton {s t : Set ℝ} {c : ℝ}
    (h : s \ t ⊆ {c}) (h' : t \ s ⊆ {c}) (f : ℝ → ℝ≥0∞) :
    ∫⁻ x in s, f x = ∫⁻ x in t, f x := by
  apply setLIntegral_congr
  rw [ae_eq_set]
  exact ⟨measure_mono_null h Real.volume_singleton,
    measure_mono_null h' Real.volume_singleton⟩

end TSDPP
