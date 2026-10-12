/-
Copyright (c) 2026 TSDPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

namespace TSDPP

/-- Chernoff/KL lower bound.

For every `μ` with `0 < μ < 2/3`, the logarithmic expression
`μ * log (2/3 + μ/2) + (1 - μ) * log (1 + μ/2)` dominates the line `(189/2000) * μ`.

The constant `189/2000 = 0.0945` is optimal up to `3.5 * 10⁻⁵`: the expression is
`0` at `μ = 0` with right-derivative `1/2 - log (3/2) ≈ 0.0945348918`, so no
constant larger than `1/2 - log (3/2)` can work. -/
theorem kl_chernoff_lower {μ : ℝ} (hμ0 : 0 < μ) (hμ : μ < 2 / 3) :
    (189 / 2000 : ℝ) * μ ≤ μ * Real.log (2 / 3 + μ / 2) + (1 - μ) * Real.log (1 + μ / 2) := by
  have hμle : (0 : ℝ) ≤ μ := le_of_lt hμ0
  -- A second-order lower bound for `log (1 + y)`, valid for `y ≥ 0`.
  have hA : ∀ y : ℝ, 0 ≤ y → y - y ^ 2 / 2 ≤ Real.log (1 + y) := by
    intro y hy
    have hpos : 0 < y + 2 := by linarith
    have hquad : y - y ^ 2 / 2 ≤ 2 * y / (y + 2) := by
      rw [le_div_iff₀ hpos]
      nlinarith [pow_nonneg hy 3]
    exact hquad.trans (Real.le_log_one_add_of_nonneg hy)
  have h1 : μ / 2 - (μ / 2) ^ 2 / 2 ≤ Real.log (1 + μ / 2) := hA (μ / 2) (by linarith)
  have h2 : 3 * μ / 4 - (3 * μ / 4) ^ 2 / 2 ≤ Real.log (1 + 3 * μ / 4) :=
    hA (3 * μ / 4) (by linarith)
  have hsplit : Real.log (2 / 3 + μ / 2) = Real.log (2 / 3) + Real.log (1 + 3 * μ / 4) := by
    have h : (2 / 3 : ℝ) + μ / 2 = 2 / 3 * (1 + 3 * μ / 4) := by ring
    rw [h, Real.log_mul (by norm_num) (by linarith)]
  have h2' : Real.log (2 / 3) + (3 * μ / 4 - (3 * μ / 4) ^ 2 / 2) ≤ Real.log (2 / 3 + μ / 2) := by
    rw [hsplit]
    linarith
  have hlog23 : Real.log (2 / 3 : ℝ) = -Real.log (3 / 2) := by
    rw [show (2 / 3 : ℝ) = (3 / 2)⁻¹ by norm_num, Real.log_inv]
  have hmul1 : μ * (Real.log (2 / 3) + (3 * μ / 4 - (3 * μ / 4) ^ 2 / 2))
      ≤ μ * Real.log (2 / 3 + μ / 2) :=
    mul_le_mul_of_nonneg_left h2' hμle
  have hmul2 : (1 - μ) * (μ / 2 - (μ / 2) ^ 2 / 2) ≤ (1 - μ) * Real.log (1 + μ / 2) :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  have htotal := add_le_add hmul1 hmul2
  -- Rational upper bound on `log (3/2)` from Mathlib's decimal bounds on `log 2`, `log 3`.
  have hlog32 : Real.log (3 / 2) < 0.4055 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    linarith [Real.log_three_lt_d9, Real.log_two_gt_d9]
  have hL : (189 / 2000 : ℝ) ≤ 1 / 2 - Real.log (3 / 2) := by linarith
  have hquad : (0 : ℝ) ≤ μ ^ 2 * (4 - 5 * μ) / 32 := by
    have h4 : (0 : ℝ) < 4 - 5 * μ := by linarith
    exact div_nonneg (mul_nonneg (sq_nonneg μ) h4.le) (by norm_num)
  have hid : μ * (Real.log (2 / 3) + (3 * μ / 4 - (3 * μ / 4) ^ 2 / 2))
        + (1 - μ) * (μ / 2 - (μ / 2) ^ 2 / 2)
      = μ * (1 / 2 - Real.log (3 / 2)) + μ ^ 2 * (4 - 5 * μ) / 32 := by
    rw [hlog23]
    ring
  have hkey : (189 / 2000 : ℝ) * μ
      ≤ μ * (Real.log (2 / 3) + (3 * μ / 4 - (3 * μ / 4) ^ 2 / 2))
        + (1 - μ) * (μ / 2 - (μ / 2) ^ 2 / 2) := by
    rw [hid]
    have hμL : (189 / 2000 : ℝ) * μ ≤ (1 / 2 - Real.log (3 / 2)) * μ :=
      mul_le_mul_of_nonneg_right hL hμle
    linarith
  linarith

end TSDPP
