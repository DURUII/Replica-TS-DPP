import Mathlib

open scoped ENNReal

namespace Scratch

/-- `(100/101)^100 ≤ 2/5`. -/
theorem pow_100_101_le : ((100 : ℝ) / 101) ^ 100 ≤ 2 / 5 := by
  -- log(100/101) ≤ -1/101, from log ≤ x-1 at x = 100/101.
  have hlog : Real.log (100 / 101 : ℝ) ≤ -(1 / 101 : ℝ) := by
    have hle := Real.log_le_sub_one_of_pos (x := (100 / 101 : ℝ)) (by norm_num)
    have hsub : (100 / 101 : ℝ) - 1 = -(1 / 101 : ℝ) := by norm_num
    simpa [hsub] using hle
  have hmul : (100 : ℝ) * Real.log (100 / 101 : ℝ) ≤ -(100 / 101 : ℝ) := by
    calc
      (100 : ℝ) * Real.log (100 / 101 : ℝ) ≤ (100 : ℝ) * -(1 / 101 : ℝ) :=
        mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 100)
      _ = -(100 / 101 : ℝ) := by norm_num
  -- (100/101)^100 ≤ exp(-100/101)
  have h1 : ((100 : ℝ) / 101) ^ 100 ≤ Real.exp (-(100 / 101 : ℝ)) := by
    rw [← Real.log_le_iff_le_exp (show (0 : ℝ) < ((100 : ℝ) / 101) ^ 100 from pow_pos (by norm_num) 100)]
    rw [Real.log_pow]
    exact hmul
  -- exp(-100/101) ≤ 2/5, i.e. 5/2 ≤ exp(100/101) via the 4-term Taylor sum.
  have h52 : (5 / 2 : ℝ) ≤ Real.exp (100 / 101 : ℝ) := by
    have hsum := Real.sum_le_exp_of_nonneg (x := (100 / 101 : ℝ)) (by norm_num) 4
    have hsum' : (5 / 2 : ℝ) ≤ ∑ i ∈ Finset.range 4, (100 / 101 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    exact hsum'.trans hsum
  have h2 : Real.exp (-(100 / 101 : ℝ)) ≤ 2 / 5 := by
    rw [Real.exp_neg]
    rw [← one_div (Real.exp (100 / 101 : ℝ))]
    rw [div_le_iff₀ (Real.exp_pos (100 / 101 : ℝ))]
    calc
      1 = (2 / 5 : ℝ) * (5 / 2 : ℝ) := by norm_num
      _ ≤ (2 / 5 : ℝ) * Real.exp (100 / 101 : ℝ) :=
        mul_le_mul_of_nonneg_left h52 (by norm_num : (0 : ℝ) ≤ 2 / 5)
  exact h1.trans h2

/-- `exp(-750/43) ≤ (86/101)^100`. -/
theorem exp_neg_le_pow_86_101 : Real.exp (-(750 / 43 : ℝ)) ≤ ((86 : ℝ) / 101) ^ 100 := by
  -- log(86/101) ≥ -15/86, from log(101/86) ≤ 15/86.
  have hlog : -(15 / 86 : ℝ) ≤ Real.log (86 / 101 : ℝ) := by
    have hle := Real.log_le_sub_one_of_pos (x := (101 / 86 : ℝ)) (by norm_num)
    have hsub : (101 / 86 : ℝ) - 1 = 15 / 86 := by norm_num
    have hle' : Real.log (101 / 86 : ℝ) ≤ 15 / 86 := by
      simpa [hsub] using hle
    have hinv : Real.log (86 / 101 : ℝ) = -Real.log (101 / 86 : ℝ) := by
      have h86 : (86 / 101 : ℝ) = (101 / 86 : ℝ)⁻¹ := by norm_num
      rw [h86, Real.log_inv]
    rw [hinv, neg_le_neg_iff]
    exact hle'
  have hmul : -(750 / 43 : ℝ) ≤ (100 : ℝ) * Real.log (86 / 101 : ℝ) := by
    have hle' := mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 100)
    have hnorm : -(750 / 43 : ℝ) = (100 : ℝ) * -(15 / 86 : ℝ) := by norm_num
    rwa [hnorm]
  -- exp(-750/43) ≤ (86/101)^100
  rw [← Real.le_log_iff_exp_le (show (0 : ℝ) < ((86 : ℝ) / 101) ^ 100 from pow_pos (by norm_num) 100)]
  rw [Real.log_pow]
  exact hmul

/-- `2·exp(-539/25) < (3/5)·exp(-750/43)`. -/
theorem arith_core :
    2 * Real.exp (-(539 / 25 : ℝ)) < (3 / 5 : ℝ) * Real.exp (-(750 / 43 : ℝ)) := by
  have hkey : (10 / 3 : ℝ) < Real.exp (4427 / 1075 : ℝ) := by
    have h := Real.add_one_le_exp (4427 / 1075 : ℝ)
    have h' : (10 / 3 : ℝ) < (4427 / 1075 : ℝ) + 1 := by norm_num
    exact h'.trans_le h
  have hlt : Real.exp (-(4427 / 1075 : ℝ)) < 3 / 10 := by
    rw [Real.exp_neg]
    rw [← one_div (Real.exp (4427 / 1075 : ℝ))]
    rw [div_lt_iff₀ (Real.exp_pos (4427 / 1075 : ℝ))]
    calc
      1 = (3 / 10 : ℝ) * (10 / 3 : ℝ) := by norm_num
      _ < (3 / 10 : ℝ) * Real.exp (4427 / 1075 : ℝ) :=
        mul_lt_mul_of_pos_left hkey (by norm_num : (0 : ℝ) < 3 / 10)
  have hlt2 : 2 * Real.exp (-(4427 / 1075 : ℝ)) < 3 / 5 := by
    have h := mul_lt_mul_of_pos_left hlt (by norm_num : (0 : ℝ) < 2)
    have h2 : 2 * (3 / 10 : ℝ) = 3 / 5 := by norm_num
    simpa [h2] using h
  have hsplit : -(539 / 25 : ℝ) = -(4427 / 1075 : ℝ) + -(750 / 43 : ℝ) := by norm_num
  calc
    2 * Real.exp (-(539 / 25 : ℝ)) = (2 * Real.exp (-(4427 / 1075 : ℝ))) * Real.exp (-(750 / 43 : ℝ)) := by
      rw [hsplit, Real.exp_add]
      ring
    _ < (3 / 5 : ℝ) * Real.exp (-(750 / 43 : ℝ)) :=
      mul_lt_mul_of_pos_right hlt2 (Real.exp_pos (-(750 / 43 : ℝ)))

/-- The combination I actually need. -/
theorem refute_arith :
    2 * Real.exp (-(539 / 25 : ℝ))
      < ((86 : ℝ) / 101) ^ 100 * (1 - ((100 : ℝ) / 101) ^ 100) := by
  have hle35 : (3 / 5 : ℝ) ≤ 1 - ((100 : ℝ) / 101) ^ 100 := by
    nlinarith [pow_100_101_le]
  have hpos_pow : (0 : ℝ) ≤ ((86 : ℝ) / 101) ^ 100 := by
    exact pow_nonneg (by norm_num : (0 : ℝ) ≤ 86 / 101) 100
  have hprod := mul_le_mul exp_neg_le_pow_86_101 hle35 (by norm_num : (0 : ℝ) ≤ 3 / 5) hpos_pow
  exact lt_of_lt_of_le arith_core (by simpa [mul_comm] using hprod)

end Scratch
