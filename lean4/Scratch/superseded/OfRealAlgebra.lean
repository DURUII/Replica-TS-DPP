/-
Copyright (c) 2026 TSDPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TSDPP

/-- Pointwise algebra for the Gamma-ratio computation: for `u > 0`, `0 < r < 1`,
`ofReal u * (gammaPDF a 1 (u - u*r) * gammaPDF b 1 (u*r))` factors as
`ofReal ((1-r)^(a-1) * r^(b-1) / (Γ a * Γ b)) * ofReal (u^(a+b-1) * exp(-u))`. -/
theorem gammaPDF_mul_factor (a b r u : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hu : 0 < u) (hr : 0 < r) (hr1 : r < 1) :
    ENNReal.ofReal u * (gammaPDF a 1 (u - u * r) * gammaPDF b 1 (u * r))
      = ENNReal.ofReal ((1 - r) ^ (a - 1) * r ^ (b - 1) / (Real.Gamma a * Real.Gamma b))
        * ENNReal.ofReal (u ^ (a + b - 1) * Real.exp (-u)) := by
  have h3 : 0 ≤ u - u * r := by
    have h : u - u * r = u * (1 - r) := by ring
    rw [h]
    exact mul_nonneg hu.le (by linarith)
  have h4 : 0 ≤ u * r := mul_nonneg hu.le hr.le
  have hA1 : 0 ≤ (u - u * r) ^ (a - 1) * Real.exp (-(u - u * r)) / Real.Gamma a :=
    div_nonneg (mul_nonneg (Real.rpow_nonneg h3 _) (Real.exp_nonneg _)) (by positivity)
  have hA2 : 0 ≤ (u * r) ^ (b - 1) * Real.exp (-(u * r)) / Real.Gamma b :=
    div_nonneg (mul_nonneg (Real.rpow_nonneg h4 _) (Real.exp_nonneg _)) (by positivity)
  have hT : 0 ≤ u ^ (a + b - 1) * Real.exp (-u) :=
    mul_nonneg (Real.rpow_nonneg hu.le _) (Real.exp_nonneg _)
  have hg1 : gammaPDF a 1 (u - u * r)
      = ENNReal.ofReal ((u - u * r) ^ (a - 1) * Real.exp (-(u - u * r)) / Real.Gamma a) := by
    rw [gammaPDF_of_nonneg h3, Real.one_rpow, one_mul]
    congr 1
    ring
  have hg2 : gammaPDF b 1 (u * r)
      = ENNReal.ofReal ((u * r) ^ (b - 1) * Real.exp (-(u * r)) / Real.Gamma b) := by
    rw [gammaPDF_of_nonneg h4, Real.one_rpow, one_mul]
    congr 1
    ring
  have h1r : (0 : ℝ) ≤ 1 - r := by linarith
  have hpow : u ^ (a + b - 1) = u * u ^ (a - 1) * u ^ (b - 1) := by
    have hA : u ^ (a + b - 1) = u ^ a * u ^ (b - 1) := by
      conv_lhs => rw [show a + b - 1 = a + (b - 1) by ring]
      rw [Real.rpow_add hu]
    have hB : u ^ a = u * u ^ (a - 1) := by
      conv_lhs => rw [show a = 1 + (a - 1) by ring]
      rw [Real.rpow_add hu, Real.rpow_one]
    rw [hA, hB]
  have hexp : Real.exp (-u) = Real.exp (-(u * (1 - r))) * Real.exp (-(u * r)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hg1, hg2, ← ENNReal.ofReal_mul hA1, ← ENNReal.ofReal_mul hu.le,
    ← ENNReal.ofReal_mul' hT]
  congr 1
  rw [show u - u * r = u * (1 - r) by ring]
  rw [Real.mul_rpow hu.le h1r]
  rw [Real.mul_rpow hu.le hr.le]
  rw [hpow, hexp]
  ring

/-- Same, but in the form where the `u`-integral has already been separated:
for `u > 0` and `0 < r < 1`,
`ofReal u * (gammaPDF a 1 (u - u*r) * gammaPDF b 1 (u*r))`
`= ofReal ((1-r)^(a-1) * r^(b-1) /(Γ a * Γ b)) * ofReal (u^(a+b-1) * exp(-u))`. -/
theorem gammaPDF_mul_factor' (a b r u : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hu : 0 < u) (hr : 0 < r) (hr1 : r < 1) :
    ENNReal.ofReal u * (gammaPDF a 1 (u - u * r) * gammaPDF b 1 (u * r))
      = ENNReal.ofReal ((1 - r) ^ (a - 1) * r ^ (b - 1) / (Real.Gamma a * Real.Gamma b)
          * (u ^ (a + b - 1) * Real.exp (-u))) := by
  rw [gammaPDF_mul_factor a b r u ha hb hu hr hr1]
  have hS : 0 ≤ (1 - r) ^ (a - 1) * r ^ (b - 1) / (Real.Gamma a * Real.Gamma b) :=
    div_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ 1 - r) _)
      (Real.rpow_nonneg hr.le _)) (by positivity)
  exact (ENNReal.ofReal_mul hS).symm

end TSDPP
