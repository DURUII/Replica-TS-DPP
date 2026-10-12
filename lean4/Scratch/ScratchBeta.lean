/-
Copyright (c) 2026 TSDPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Set

namespace TSDPP

/-- The Beta law of the upper tail. -/
theorem betaMeasure_Ici (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (ht0 : 0 < t) (ht1 : t < 1) :
    betaMeasure a b (Ici t)
      = ENNReal.ofReal (Real.Gamma (a + b) / (Real.Gamma a * Real.Gamma b))
        * ∫⁻ w in Set.Icc t 1, ENNReal.ofReal (w ^ (a - 1) * (1 - w) ^ (b - 1)) := by
  have hc : 0 ≤ (1 : ℝ) / beta a b := le_of_lt (one_div_pos.mpr (beta_pos ha hb))
  have hg : Measurable fun w : ℝ => ENNReal.ofReal (w ^ (a - 1) * (1 - w) ^ (b - 1)) := by
    fun_prop
  have hconst : (1 : ℝ) / beta a b = Real.Gamma (a + b) / (Real.Gamma a * Real.Gamma b) := by
    simp only [beta, one_div, inv_div]
  have hdisj₁ : Disjoint (Set.Ico t 1) (Set.Ici (1 : ℝ)) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    simp only [Set.mem_Ico] at hx1
    simp only [Set.mem_Ici] at hx2
    linarith
  have hdisj₂ : Disjoint (Set.Ico t 1) ({1} : Set ℝ) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    simp only [Set.mem_Ico] at hx1
    simp only [Set.mem_singleton_iff] at hx2
    linarith
  rw [betaMeasure, withDensity_apply _ measurableSet_Ici]
  have hIci : ∫⁻ w in Set.Ici t, betaPDF a b w = ∫⁻ w in Set.Ico t 1, betaPDF a b w := by
    rw [← Set.Ico_union_Ici_eq_Ici ht1.le,
      lintegral_union measurableSet_Ici hdisj₁,
      show ∫⁻ w in Set.Ici (1 : ℝ), betaPDF a b w = 0 from
        setLIntegral_eq_zero measurableSet_Ici (fun x hx => betaPDF_eq_zero_of_one_le hx),
      add_zero]
  rw [hIci]
  have hsplit : ∫⁻ w in Set.Ico t 1, betaPDF a b w
      = ∫⁻ w in Set.Ico t 1,
          ENNReal.ofReal (1 / beta a b) * ENNReal.ofReal (w ^ (a - 1) * (1 - w) ^ (b - 1)) := by
    refine setLIntegral_congr_fun measurableSet_Ico (fun x hx => ?_)
    rw [betaPDF_of_pos_lt_one (by linarith [hx.1]) hx.2, mul_assoc, ENNReal.ofReal_mul hc]
  rw [hsplit]
  rw [lintegral_const_mul (ENNReal.ofReal (1 / beta a b)) hg]
  have hIcoIcc : ∫⁻ w in Set.Ico t 1, ENNReal.ofReal (w ^ (a - 1) * (1 - w) ^ (b - 1))
      = ∫⁻ w in Set.Icc t 1, ENNReal.ofReal (w ^ (a - 1) * (1 - w) ^ (b - 1)) := by
    rw [← Set.Ico_union_right ht1.le,
      lintegral_union (measurableSet_singleton 1) hdisj₂,
      show ∫⁻ w in ({1} : Set ℝ), ENNReal.ofReal (w ^ (a - 1) * (1 - w) ^ (b - 1)) = 0 from by
        simp [Measure.restrict_eq_zero.mpr Real.volume_singleton],
      add_zero]
  rw [hIcoIcc, hconst]

end TSDPP
