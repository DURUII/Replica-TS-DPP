import Mathlib

namespace TSDPP

/-- `(1 - t/n)^n ≤ exp(-t)` for real `n > 0`, `0 ≤ t ≤ n`.
Derived from `Real.log_le_sub_one_of_pos`; the Mathlib lemma
`Real.one_sub_div_pow_le_exp_neg` handles only *natural* `n`. -/
private lemma rpow_one_sub_div_le_exp_neg {n t : ℝ} (hn : 0 < n) (htn : t ≤ n) :
    (1 - t / n) ^ n ≤ Real.exp (-t) := by
  have hb : 0 ≤ 1 - t / n := sub_nonneg.2 ((div_le_one hn).2 htn)
  rcases hb.eq_or_lt with h | h
  · rw [← h, Real.zero_rpow (ne_of_gt hn)]
    exact (Real.exp_pos (-t)).le
  · have hlog := Real.log_le_sub_one_of_pos h
    have h4 : Real.log (1 - t / n) * n ≤ -t := by
      have hm := mul_le_mul_of_nonneg_right hlog hn.le
      have hthis : ((1 - t / n) - 1) * n = -t := by field_simp; ring
      linarith
    rw [Real.rpow_def_of_pos h]
    exact Real.exp_le_exp.2 h4

/-- `(1 + t/n)^n ≤ exp t` for real `n > 0`. Companion of the above. -/
private lemma rpow_one_add_div_le_exp {n t : ℝ} (hn : 0 < n) (ht : 0 ≤ t) :
    (1 + t / n) ^ n ≤ Real.exp t := by
  have hb : 0 < 1 + t / n := by
    have : 0 ≤ t / n := div_nonneg ht hn.le
    linarith
  have hlog := Real.log_le_sub_one_of_pos hb
  have h4 : Real.log (1 + t / n) * n ≤ t := by
    have hm := mul_le_mul_of_nonneg_right hlog hn.le
    have hthis : ((1 + t / n) - 1) * n = t := by field_simp; ring
    linarith
  rw [Real.rpow_def_of_pos hb]
  exact Real.exp_le_exp.2 h4

/-- `x * (1/x)^y = x^(1-y)` for `x > 0`. -/
private lemma mul_inv_rpow (x y : ℝ) (hx : 0 < x) : x * (1 / x) ^ y = x ^ (1 - y) := by
  rw [Real.rpow_sub hx, Real.rpow_one, one_div, Real.inv_rpow hx.le, div_eq_mul_inv]

/-- `79/50 ≤ exp(47/100)`, from the 4th partial sum of `exp`. -/
private lemma numA_aux : (1 + 29/50 : ℝ) ≤ Real.exp (47/100) := by
  have h := Real.sum_le_exp_of_nonneg (x := (47 : ℝ) / 100) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `(1 + 29/50) * exp(-(29/50)) ≤ exp(-(11/100))`; margin 1.26%. -/
private lemma numA : (1 + 29/50 : ℝ) * Real.exp (-(29/50)) ≤ Real.exp (-(11/100)) := by
  have hp : (0 : ℝ) < Real.exp (29/50) := Real.exp_pos _
  have key : (1 + 29/50 : ℝ) ≤ Real.exp (-(11/100)) * Real.exp (29/50) := by
    rw [← Real.exp_add]
    have harg : -((11 : ℝ) / 100) + 29/50 = 47/100 := by norm_num
    rw [harg]
    exact numA_aux
  calc (1 + 29/50 : ℝ) * Real.exp (-(29/50))
      = (1 + 29/50) / Real.exp (29/50) := by rw [Real.exp_neg]; rfl
    _ ≤ Real.exp (-(11/100)) := (div_le_iff₀ hp).2 key

/-- `exp(53/100) ≤ 50/29`, from the 4th partial sum plus the `exp_bound'` remainder. -/
private lemma numB_aux : Real.exp (53/100) ≤ 50/29 := by
  have h := Real.exp_bound' (x := (53 : ℝ) / 100) (by norm_num) (by norm_num) (n := 4)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `29/50 ≤ exp(-(53/100))`, i.e. `exp(53/100) ≤ 50/29`. -/
private lemma numB1 : (29/50 : ℝ) ≤ Real.exp (-(53/100)) := by
  rw [Real.exp_neg, inv_eq_one_div, le_div_iff₀ (Real.exp_pos (53/100))]
  nlinarith [numB_aux]

/-- `(29/50) * exp(21/50) ≤ exp(-(11/100))`; margin 1.48%. -/
private lemma numB : (29/50 : ℝ) * Real.exp (21/50) ≤ Real.exp (-(11/100)) := by
  have h := mul_le_mul_of_nonneg_right numB1 (Real.exp_pos (21/50)).le
  have harg : -((53 : ℝ) / 100) + 21/50 = -((11 : ℝ) / 100) := by norm_num
  rwa [← Real.exp_add, harg] at h

/-- Union-bound witness for the Beta concentration inequality (see DESIGN.md GAP-2d). -/
theorem unionWitness (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧
      (1 + ρ * s) * (1 - s) ^ ρ ≤ Real.exp (-(11/100)) ∧
      (ρ * s) * (1 / ρ + 1 - s) ^ ρ ≤ Real.exp (-(11/100)) := by
  refine ⟨min 1 (29 / (50 * ρ)), lt_min one_pos (by positivity), min_le_left _ _, ?_, ?_⟩
  · have hρne : ρ ≠ 0 := ne_of_gt hρ
    rcases le_or_gt (29 / (50 * ρ)) 1 with h | h
    · rw [min_eq_right h]
      have h50 : 29 ≤ 50 * ρ := (div_le_one (by positivity : (0 : ℝ) < 50 * ρ)).1 h
      have hge : (29 : ℝ) / 50 ≤ ρ := by linarith
      have hs : (29 : ℝ) / (50 * ρ) = (29/50) / ρ := by ring
      have hA1 : ρ * (29 / (50 * ρ)) = 29/50 := by field_simp; try ring
      rw [hA1, hs]
      have hle : (1 - (29/50) / ρ) ^ ρ ≤ Real.exp (-(29/50)) :=
        rpow_one_sub_div_le_exp_neg hρ hge
      exact (mul_le_mul_of_nonneg_left hle (by norm_num : (0 : ℝ) ≤ 1 + 29/50)).trans numA
    · rw [min_eq_left h.le]
      have h0 : (1 - 1 : ℝ) ^ ρ = 0 := by rw [sub_self, Real.zero_rpow hρne]
      rw [mul_one, h0, mul_zero]
      exact (Real.exp_pos _).le
  · have hρne : ρ ≠ 0 := ne_of_gt hρ
    rcases le_or_gt (29 / (50 * ρ)) 1 with h | h
    · rw [min_eq_right h]
      have h50 : 29 ≤ 50 * ρ := (div_le_one (by positivity : (0 : ℝ) < 50 * ρ)).1 h
      have hge : (29 : ℝ) / 50 ≤ ρ := by linarith
      have hs : (29 : ℝ) / (50 * ρ) = (29/50) / ρ := by ring
      have hA1 : ρ * (29 / (50 * ρ)) = 29/50 := by field_simp; try ring
      rw [hA1, hs]
      have hbase : 1 / ρ + 1 - (29/50) / ρ = 1 + (21/50) / ρ := by ring
      rw [hbase]
      have hle2 : (1 + (21/50) / ρ) ^ ρ ≤ Real.exp (21/50) := rpow_one_add_div_le_exp hρ (by norm_num)
      exact (mul_le_mul_of_nonneg_left hle2 (by norm_num : (0 : ℝ) ≤ 29/50)).trans numB
    · rw [min_eq_left h.le]
      have h29 : 50 * ρ ≤ 29 := (one_le_div (by positivity : (0 : ℝ) < 50 * ρ)).1 h.le
      have hle : ρ ≤ 29/50 := by linarith
      have hbase : 1 / ρ + 1 - 1 = 1 / ρ := by ring
      rw [mul_one, hbase, mul_inv_rpow ρ ρ hρ]
      have h1m : (0 : ℝ) ≤ 1 - ρ := by linarith
      have h1m' : (21 : ℝ) / 50 ≤ 1 - ρ := by linarith
      have hbound : Real.log ρ * (1 - ρ) ≤ -((21 : ℝ) / 50) ^ 2 := by
        have hlog := Real.log_le_sub_one_of_pos hρ
        have hm : Real.log ρ * (1 - ρ) ≤ (ρ - 1) * (1 - ρ) :=
          mul_le_mul_of_nonneg_right hlog h1m
        have h2 : (ρ - 1) * (1 - ρ) = -((1 - ρ) ^ 2) := by ring
        have h3 : ((21 : ℝ) / 50) ^ 2 ≤ (1 - ρ) ^ 2 := by
          nlinarith [sq_nonneg ((1 - ρ) - 21/50), h1m']
        linarith
      calc ρ ^ (1 - ρ) = Real.exp (Real.log ρ * (1 - ρ)) := Real.rpow_def_of_pos hρ _
        _ ≤ Real.exp (-((21 : ℝ) / 50) ^ 2) := Real.exp_le_exp.2 hbound
        _ ≤ Real.exp (-(11/100)) := by
              apply Real.exp_le_exp.2
              norm_num

#print axioms TSDPP.unionWitness

end TSDPP
