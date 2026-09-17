import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Set

namespace TSDPP

example (f : ℝ → ℝ≥0∞) (r : ℝ) (hr : 0 < r) :
    (Ioi (0:ℝ)).indicator f r = f r := by
  rw [Set.indicator_of_mem hr]

example (f : ℝ → ℝ≥0∞) (r : ℝ) (hr : 0 < r) :
    (Ioi (0:ℝ)).indicator f r = f r := by
  exact Set.indicator_of_mem hr _

example (K : ℝ → ℝ≥0∞) (u : ℝ) (hu : 0 < u) :
    (∫⁻ r, (if 0 < u then K r else 0)) = ∫⁻ r, K r := by
  rw [ite_eq_left hu]

example (K : ℝ → ℝ≥0∞) (u : ℝ) (hu : 0 < u) :
    (∫⁻ r, (if 0 < u then K r else 0)) = ∫⁻ r, K r := by
  simp only [ite_eq_left hu]

example (K : ℝ → ℝ≥0∞) (u : ℝ) (hu : 0 < u) :
    (∫⁻ r, (if 0 < u then K r else 0)) = ∫⁻ r, K r := by
  refine lintegral_congr fun r => ?_
  rw [ite_eq_left hu]

end TSDPP
