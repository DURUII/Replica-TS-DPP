/-
Copyright: formal artifact for INFOCOM'26 `infocom26.pdf`.
Released under Apache 2.0 license as described in the file LICENSE.

# R14 — the finite-sum assembly, paper Eq (39)

Eq (39) of the paper is the first of the two terms in the final regret bound:

  `Σ_{l=1}^m L·√(8 log T/η_l) ≤ L·√(8 log T/η)·2√m`.

It is *pure arithmetic*: nothing about bandits enters.  Two inequalities compose.

1. **`sum_range_inv_sqrt_le`** — `Σ_{l<m} 1/√(l+1) ≤ 2√m`.  This is where the paper's
   `2√m` comes from, and it is sharp: the numeric falsifier (`scripts/numeric_check.py`,
   row "Eq(39)") confirms `max_m (Σ_{l<m} 1/√(l+1))/(2√m) = 0.9885`.  The proof uses the
   telescoping estimate `1/√(l+1) ≤ 2(√(l+1) − √l)`, whose right-hand side sums to exactly
   `2√m` because `√(l+1) − √l = 1/(√(l+1) + √l)` and `√l ≤ √(l+1)`.
2. **Corollary 1 of the paper** — `α^l ≥ η·l` — turns `√(8 log T/α^l)` into
   `√(8 log T/(η l))`, at which point (1) applies verbatim.

`sum_inv_sqrt_weighted` records the composite form used in Eq (38).
-/
import Mathlib

namespace TSDPP

open Finset

/-- The telescoping estimate behind Eq (39): `1/√(l+1) ≤ 2(√(l+1) − √l)`.

Writing `√(l+1) − √l = 1/(√(l+1) + √l)` (multiply by the conjugate; the denominator is
positive), the claim becomes `1/√(l+1) ≤ 2/(√(l+1) + √l)`, i.e. `√(l+1) + √l ≤ 2√(l+1)`,
i.e. `√l ≤ √(l+1)` — monotonicity of `√` on non-negative reals. -/
lemma inv_sqrt_le_two_mul_sub (l : ℕ) :
    1 / Real.sqrt ((l : ℝ) + 1) ≤ 2 * (Real.sqrt ((l : ℝ) + 1) - Real.sqrt (l : ℝ)) := by
  have hA : 0 < (l : ℝ) + 1 := by positivity
  have hB : 0 ≤ (l : ℝ) := Nat.cast_nonneg l
  have hsA : 0 < Real.sqrt ((l : ℝ) + 1) := Real.sqrt_pos.mpr hA
  have hsl : 0 ≤ Real.sqrt (l : ℝ) := Real.sqrt_nonneg _
  have hsum : 0 < Real.sqrt ((l : ℝ) + 1) + Real.sqrt (l : ℝ) := by linarith
  have hdiff : 1 / (Real.sqrt ((l : ℝ) + 1) + Real.sqrt (l : ℝ))
      = Real.sqrt ((l : ℝ) + 1) - Real.sqrt (l : ℝ) := by
    rw [div_eq_iff (ne_of_gt hsum)]
    have hconj : (Real.sqrt ((l : ℝ) + 1) - Real.sqrt (l : ℝ))
        * (Real.sqrt ((l : ℝ) + 1) + Real.sqrt (l : ℝ))
        = (Real.sqrt ((l : ℝ) + 1)) ^ 2 - (Real.sqrt (l : ℝ)) ^ 2 := by ring
    rw [hconj, Real.sq_sqrt hA.le, Real.sq_sqrt hB]
    ring
  rw [← hdiff, mul_one_div, div_le_iff₀ hsA, div_mul_eq_mul_div, le_div_iff₀ hsum]
  have hle : Real.sqrt (l : ℝ) ≤ Real.sqrt ((l : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
  linarith

/-- The telescoping sum `Σ_{l<m} (√(l+1) − √l) = √m`, proved directly by induction rather
than by invoking a `sum_range_sub` helper. -/
lemma sum_range_sqrt_sub (m : ℕ) :
    ∑ l ∈ range m, (Real.sqrt ((l : ℝ) + 1) - Real.sqrt (l : ℝ)) = Real.sqrt m := by
  induction m with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

/-- **Eq (39), arithmetic core.**  `Σ_{l<m} 1/√(l+1) ≤ 2√m`. -/
theorem sum_range_inv_sqrt_le (m : ℕ) :
    ∑ l ∈ range m, 1 / Real.sqrt ((l : ℝ) + 1) ≤ 2 * Real.sqrt m := by
  calc ∑ l ∈ range m, 1 / Real.sqrt ((l : ℝ) + 1)
      ≤ ∑ l ∈ range m, 2 * (Real.sqrt ((l : ℝ) + 1) - Real.sqrt (l : ℝ)) :=
        sum_le_sum fun l _ => inv_sqrt_le_two_mul_sub l
    _ = 2 * Real.sqrt m := by rw [← mul_sum, sum_range_sqrt_sub]

/-- **Eq (39) in the form the paper uses it.**  With `C ≥ 0` standing for `L·√(8 log T)`
and `ηl l ≥ η·(l+1) > 0` for the per-episode selection counts `α^l_i` of Corollary 1,

  `Σ_{l<m} C/√(ηl l) ≤ C/√η · 2√m`.

This is the composite step that produces the `L√(32m log T/η)` of Eq (39): the `√η` pulls
out of the sum by `Real.sqrt_mul`, and what is left is `sum_range_inv_sqrt_le`. -/
theorem sum_inv_sqrt_weighted (m : ℕ) {C η : ℝ} (hC : 0 ≤ C) (hη : 0 < η)
    (ηl : ℕ → ℝ) (hηl : ∀ l : ℕ, η * ((l : ℝ) + 1) ≤ ηl l) :
    ∑ l ∈ range m, C / Real.sqrt (ηl l)
      ≤ (C / Real.sqrt η) * (2 * Real.sqrt m) := by
  have hηpos : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have hkey : ∀ l : ℕ, (C / Real.sqrt η) * (1 / Real.sqrt ((l : ℝ) + 1))
      = C / Real.sqrt (η * ((l : ℝ) + 1)) := by
    intro l
    have h2 : Real.sqrt ((l : ℝ) + 1) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    rw [Real.sqrt_mul hη.le ((l : ℝ) + 1)]
    field_simp
  have hstep : ∀ l ∈ range m, C / Real.sqrt (ηl l)
      ≤ (C / Real.sqrt η) * (1 / Real.sqrt ((l : ℝ) + 1)) := by
    intro l _
    have hl : 0 < η * ((l : ℝ) + 1) := mul_pos hη (by positivity)
    have hmono : Real.sqrt (η * ((l : ℝ) + 1)) ≤ Real.sqrt (ηl l) :=
      Real.sqrt_le_sqrt (hηl l)
    rw [hkey l]
    rw [div_eq_mul_one_div C, div_eq_mul_one_div C]
    exact mul_le_mul_of_nonneg_left
      (one_div_le_one_div_of_le (Real.sqrt_pos.mpr hl) hmono) hC
  calc ∑ l ∈ range m, C / Real.sqrt (ηl l)
      ≤ ∑ l ∈ range m, (C / Real.sqrt η) * (1 / Real.sqrt ((l : ℝ) + 1)) :=
        sum_le_sum hstep
    _ = (C / Real.sqrt η) * ∑ l ∈ range m, 1 / Real.sqrt ((l : ℝ) + 1) := by rw [mul_sum]
    _ ≤ (C / Real.sqrt η) * (2 * Real.sqrt m) :=
        mul_le_mul_of_nonneg_left (sum_range_inv_sqrt_le m)
          (div_nonneg hC (Real.sqrt_nonneg η))

end TSDPP
