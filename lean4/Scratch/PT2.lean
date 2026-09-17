import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Set

namespace TSDPP

lemma setLIntegral_congr_of_diff_subset_singleton {s t : Set ℝ} {c : ℝ}
    (h : s \ t ⊆ {c}) (h' : t \ s ⊆ {c}) (f : ℝ → ℝ≥0∞) :
    ∫⁻ x in s, f x = ∫⁻ x in t, f x := by
  apply setLIntegral_congr
  rw [ae_eq_set]
  exact ⟨measure_mono_null h Real.volume_singleton,
    measure_mono_null h' Real.volume_singleton⟩


example (C : ℝ → ℝ≥0∞) (D : ℝ≥0∞) (t : ℝ) :
    (∫⁻ r in Ioi (0:ℝ), (if r ≤ 1 - t then C r else 0) * D)
      = ∫⁻ r in Ioc (0:ℝ) (1-t), C r * D := by
  rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioc]
  refine lintegral_congr fun r => ?_
  by_cases hr : 0 < r
  · by_cases hr1 : r ≤ 1 - t
    · rw [Set.indicator_of_mem (show r ∈ Ioi (0:ℝ) from hr),
        Set.indicator_of_mem (show r ∈ Ioc (0:ℝ) (1-t) from ⟨hr, hr1⟩)]
      rw [ite_eq_left hr1]
    · rw [Set.indicator_of_mem (show r ∈ Ioi (0:ℝ) from hr),
        Set.indicator_of_notMem (show r ∉ Ioc (0:ℝ) (1-t) from fun h => hr1 h.2)]
      rw [ite_eq_right hr1, zero_mul]
  · rw [Set.indicator_of_notMem (show r ∉ Ioi (0:ℝ) from hr),
      Set.indicator_of_notMem (show r ∉ Ioc (0:ℝ) (1-t) from fun h => hr h.1)]

example (a : ℝ) (D : ℝ≥0∞) (ha : 0 < a) (t : ℝ) (ht1 : t < 1) :
    ∫⁻ w in Ico t 1, ENNReal.ofReal (w ^ (a - 1) * (1 - w) ^ (a - 1))
      = ∫⁻ w in Icc t 1, ENNReal.ofReal (w ^ (a - 1) * (1 - w) ^ (a - 1)) := by
  exact setLIntegral_congr_of_diff_subset_singleton
    (c := 1)
    (by
      intro x hx
      simp only [Set.mem_sdiff, Set.mem_Ico, Set.mem_Icc] at hx
      exact (hx.2 ⟨hx.1.1, le_of_lt hx.1.2⟩).elim)
    (by
      intro x hx
      simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_Ico] at hx
      simp only [Set.mem_singleton_iff]
      exact le_antisymm hx.1.2 (not_lt.mp fun h => hx.2 ⟨hx.1.1, h⟩))
    (fun w => ENNReal.ofReal (w ^ (a - 1) * (1 - w) ^ (a - 1)))

example (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (ht0 : 0 < t) (ht1 : t < 1) :
    (∫⁻ r in Ioc (0 : ℝ) (1 - t), ENNReal.ofReal ((1 - r) ^ (a - 1) * r ^ (b - 1)
        / (Real.Gamma a * Real.Gamma b)) * ENNReal.ofReal (Real.Gamma (a + b)))
      = ENNReal.ofReal (Real.Gamma (a + b) / (Real.Gamma a * Real.Gamma b))
        * ∫⁻ r in Ioc (0 : ℝ) (1 - t), ENNReal.ofReal ((1 - r) ^ (a - 1) * r ^ (b - 1)) := by
  rw [show (∫⁻ r in Ioc (0 : ℝ) (1 - t), ENNReal.ofReal ((1 - r) ^ (a - 1) * r ^ (b - 1)
          / (Real.Gamma a * Real.Gamma b)) * ENNReal.ofReal (Real.Gamma (a + b)))
      = ∫⁻ r in Ioc (0 : ℝ) (1 - t), ENNReal.ofReal (Real.Gamma (a + b) / (Real.Gamma a * Real.Gamma b))
        * ENNReal.ofReal ((1 - r) ^ (a - 1) * r ^ (b - 1)) from by
    refine setLIntegral_congr_fun measurableSet_Ioc (fun r hr => ?_)
    have hr1 : 0 < r := hr.1
    have hr2 : r ≤ 1 - t := hr.2
    have hA : 0 ≤ (1 - r) ^ (a - 1) * r ^ (b - 1) :=
      mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg hr1.le _)
    have hG : 0 ≤ Real.Gamma a * Real.Gamma b :=
      le_of_lt (mul_pos (Real.Gamma_pos_of_pos ha) (Real.Gamma_pos_of_pos hb))
    have hC : 0 ≤ (1 - r) ^ (a - 1) * r ^ (b - 1) / (Real.Gamma a * Real.Gamma b) :=
      div_nonneg hA hG
    have hB : 0 ≤ Real.Gamma (a + b) / (Real.Gamma a * Real.Gamma b) :=
      div_nonneg (Real.Gamma_pos_of_pos (by linarith)).le hG
    rw [← ENNReal.ofReal_mul hC, ← ENNReal.ofReal_mul hB]
    congr 1
    ring]
  rw [lintegral_const_mul _ (by fun_prop)]

end TSDPP
