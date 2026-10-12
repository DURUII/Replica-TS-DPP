/-
Copyright (c) 2026 TSDPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# R9 — Lemma 2 (paper Eq (23), (24), (25), (26))

The paper's Lemma 2 is a *Lipschitz* statement about the belief state law `pmf` of
`TSDPP/Belief.lean`, in the parameter `θ`:

  `Σ_x |P^θ_x − P^{θ'}_x| ≤ 2δ|θ − θ'|`                          (Eq (23))
  `Σ_x x·|P^θ_x − P^{θ'}_x| ≤ (δ(δ−1)/2 + δ(λ+δ))·|θ − θ'|`      (Eq (24))

Both are proved by the mean value theorem, exactly as in the paper: the law has only
`δ + 1` nonzero entries, of which `δ` are of the form `f(θ) = θ(1−θ)^x` (`x < δ`) and one
is of the form `f(θ) = (1−θ)^δ` (the atom at `λ+δ`).  So it suffices to bound `sup|f'|`:

* `armTerm_lipschitz` : `|θ(1−θ)^x − θ'(1−θ')^x| ≤ |θ − θ'|`        — Eq (25)
* `atomTerm_lipschitz`: `|(1−θ)^δ − (1−θ')^δ| ≤ δ|θ − θ'|`            — Eq (26)

and then sum `δ` copies of the first and one copy of the second.

The analytic content of `armTerm_lipschitz` is `TSDPP.arm_deriv_abs_le_one`, which
*is* Eq (25); it is where the two Bernoulli corollaries of `TSDPP/Ineq.lean` are spent.
Note that the paper prints `f'(ξ) = (1−ξ)^{x−1}(1 − (x+1)ξ)`, which is **not** the
derivative at `x = 0` under Lean's truncated `ℕ`-subtraction (`(1−ξ)^{0−1}` is `1`, not
`(1−ξ)^{−1}`).  The statement below therefore uses the un-truncated form
`(1−θ)^x − θ·x·(1−θ)^{x−1}`, which is correct at every `x` — trap P-10.
-/
import Mathlib
import TSDPP.Ineq
import TSDPP.Belief

namespace TSDPP

open Set Finset

/-! ## The two analytic bounds -/

/-- Derivative of one non-atom entry of the belief law: `f(θ) = θ(1−θ)^x`, whose
derivative is `(1−θ)^x − θ·x·(1−θ)^{x−1}`. -/
lemma hasDerivAt_armTerm (x : ℕ) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => t * (1 - t) ^ x)
      ((1 - θ) ^ x - θ * ((x : ℝ) * (1 - θ) ^ (x - 1))) θ := by
  have h1 : HasDerivAt (fun t : ℝ => (1 - t) ^ x) (-(x : ℝ) * (1 - θ) ^ (x - 1)) θ := by
    have h : HasDerivAt (fun t : ℝ => (1 : ℝ) - t) (-1) θ := by
      have hh := (hasDerivAt_const (x := θ) (c := (1 : ℝ))).sub (hasDerivAt_id θ)
      convert hh using 1
      · funext t; rfl
      · ring
    have h2 := h.pow x
    convert h2 using 1
    ring
  have h3 := (hasDerivAt_id θ).mul h1
  convert h3 using 1
  · funext t; rfl
  · simp only [id_eq]; ring

/-- The derivative of `armTerm` rewritten in the `u = 1−θ` normal form that
`TSDPP/Ineq.lean` bounds.  Correct at `x = 0` as well as `x ≥ 1`. -/
lemma armTerm_deriv_eq (x : ℕ) (θ : ℝ) :
    (1 - θ) ^ x - θ * ((x : ℝ) * (1 - θ) ^ (x - 1))
      = ((x : ℝ) + 1) * (1 - θ) ^ x - (x : ℝ) * (1 - θ) ^ (x - 1) := by
  rcases x with _ | k
  · ring
  · have hpow : (1 - θ) ^ (k + 1) = (1 - θ) * (1 - θ) ^ k := pow_succ' _ k
    rw [hpow, Nat.add_sub_cancel]
    ring

/-- **Eq (25)**: `sup_{θ∈[0,1]} |f'(θ)| ≤ 1` for `f(θ) = θ(1−θ)^x`, in the
`u = 1−θ` normal form.  Both signs are needed; the two halves are exactly
`succ_mul_pow_sub_le_one` and `mul_pow_sub_succ_mul_pow_le_one` of `TSDPP/Ineq.lean`.

The endpoint `u = 0` (i.e. `θ = 1`) is handled separately: the Bernoulli corollaries
need `u > 0`, but at `u = 0` the expression degenerates to `0` or `±1` by direct
computation, so the bound still holds. -/
lemma arm_deriv_abs_le_one {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (x : ℕ) :
    |((x : ℝ) + 1) * u ^ x - (x : ℝ) * u ^ (x - 1)| ≤ 1 := by
  rcases eq_or_lt_of_le hu0 with h0 | hpos
  · subst h0
    rcases x with _ | k
    · norm_num
    · rcases k with _ | j
      · norm_num
      · simp
  · rcases x with _ | k
    · norm_num
    · have hA : ((k : ℝ) + 2) * u ^ (k + 1) - ((k : ℝ) + 1) * u ^ k ≤ 1 :=
        succ_mul_pow_sub_le_one hpos hu1 k
      have hB : ((k : ℝ) + 1) * u ^ k - ((k : ℝ) + 2) * u ^ (k + 1) ≤ 1 :=
        mul_pow_sub_succ_mul_pow_le_one hpos hu1 k
      have hgoal : ((↑(k + 1) : ℝ) + 1) * u ^ (k + 1) - (↑(k + 1) : ℝ) * u ^ (k + 1 - 1)
          = ((k : ℝ) + 2) * u ^ (k + 1) - ((k : ℝ) + 1) * u ^ k := by
        push_cast
        ring
      rw [hgoal, abs_le]
      exact ⟨by linarith, hA⟩

/-- **Eq (25), function form**: `f(θ) = θ(1−θ)^x` is `1`-Lipschitz on `[0,1]`. -/
lemma armTerm_lipschitz (x : ℕ) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) :
    |b * (1 - b) ^ x - a * (1 - a) ^ x| ≤ |b - a| := by
  have hdiff : ∀ t ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (fun t : ℝ => t * (1 - t) ^ x) t := by
    intro t _
    fun_prop
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖deriv (fun t : ℝ => t * (1 - t) ^ x) t‖ ≤ (1 : ℝ) := by
    intro t ht
    rw [(hasDerivAt_armTerm x t).deriv, armTerm_deriv_eq, Real.norm_eq_abs]
    exact arm_deriv_abs_le_one (u := 1 - t) (by linarith [ht.2]) (by linarith [ht.1]) x
  have h := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le hdiff hbound ha hb
  simpa using h

/-- **Eq (26)**: `f(θ) = (1−θ)^δ` is `δ`-Lipschitz on `[0,1]`.

Proved from `abs_pow_sub_pow_le` rather than by a second mean-value argument: for
`u, v ∈ [0,1]` the general bound `|u^δ − v^δ| ≤ |u−v|·δ·max|u||v|^{δ−1}` collapses to
`δ|u−v|` because `max|u||v| ≤ 1`. -/
lemma atomTerm_lipschitz (δ : ℕ) {θ θ' : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hθ' : θ' ∈ Icc (0 : ℝ) 1) :
    |(1 - θ) ^ δ - (1 - θ') ^ δ| ≤ (δ : ℝ) * |θ - θ'| := by
  have hu : |1 - θ| ≤ 1 := abs_le.mpr ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  have hv : |1 - θ'| ≤ 1 := abs_le.mpr ⟨by linarith [hθ'.2], by linarith [hθ'.1]⟩
  have hmax : max |1 - θ| |1 - θ'| ^ (δ - 1) ≤ 1 := by
    rcases Nat.eq_zero_or_pos δ with h | h
    · subst h; simp
    · calc max |1 - θ| |1 - θ'| ^ (δ - 1) ≤ 1 ^ (δ - 1) :=
            pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg _)) (max_le hu hv) (δ - 1)
          _ = 1 := one_pow _
  have h := abs_pow_sub_pow_le (a := 1 - θ) (b := 1 - θ') δ
  have hsub : |(1 - θ) - (1 - θ')| = |θ - θ'| := by
    rw [show (1 : ℝ) - θ - (1 - θ') = θ' - θ by ring, abs_sub_comm]
  rw [hsub] at h
  calc |(1 - θ) ^ δ - (1 - θ') ^ δ|
      ≤ |θ - θ'| * (δ : ℝ) * max |1 - θ| |1 - θ'| ^ (δ - 1) := h
    _ ≤ |θ - θ'| * (δ : ℝ) * 1 := mul_le_mul_of_nonneg_left hmax (by positivity)
    _ = (δ : ℝ) * |θ - θ'| := by ring

/-! ## Summing over the support

The law `pmf θ λ δ` is supported on `{0,…,λ+δ}`, and on all of it except the singleton
`{λ+δ}` it is `θ(1−θ)^x`.  So the sums of Eq (23) and (24) split into `δ` copies of the
`armTerm` bound plus one `atomTerm` bound. -/

/-- Restricting the sum to `range δ` loses nothing: the `δ ≤ x < λ+δ` entries are zero. -/
lemma abs_pmf_sum_range_eq (θ θ' : ℝ) (lam δ : ℕ) :
    ∑ x ∈ range (lam + δ), |pmf θ lam δ x - pmf θ' lam δ x|
      = ∑ x ∈ range δ, |pmf θ lam δ x - pmf θ' lam δ x| := by
  exact (sum_subset (s₁ := range δ) (s₂ := range (lam + δ))
    (f := fun x => |pmf θ lam δ x - pmf θ' lam δ x|)
    (fun x hx => by simp only [Finset.mem_range] at hx ⊢; omega)
    (fun x hx2 hx => by
      simp only [Finset.mem_range] at hx hx2
      rw [pmf_of_other hx (by omega), pmf_of_other hx (by omega), sub_zero, abs_zero])).symm

/-- The same restriction, weighted by `x`. -/
lemma weighted_abs_pmf_sum_range_eq (θ θ' : ℝ) (lam δ : ℕ) :
    ∑ x ∈ range (lam + δ), (x : ℝ) * |pmf θ lam δ x - pmf θ' lam δ x|
      = ∑ x ∈ range δ, (x : ℝ) * |pmf θ lam δ x - pmf θ' lam δ x| := by
  exact (sum_subset (s₁ := range δ) (s₂ := range (lam + δ))
    (f := fun x => (x : ℝ) * |pmf θ lam δ x - pmf θ' lam δ x|)
    (fun x hx => by simp only [Finset.mem_range] at hx ⊢; omega)
    (fun x hx2 hx => by
      simp only [Finset.mem_range] at hx hx2
      rw [pmf_of_other hx (by omega), pmf_of_other hx (by omega), sub_zero, abs_zero,
        mul_zero])).symm

/-- `Σ_{x<δ} x = δ(δ−1)/2` over `ℝ`.  Stated doubled, because `Nat` division is awkward to
cast and this is the only shape the proof needs. -/
lemma two_mul_sum_range_cast_id (δ : ℕ) :
    2 * ∑ x ∈ range δ, (x : ℝ) = (δ : ℝ) * ((δ : ℝ) - 1) := by
  induction δ with
  | zero => simp
  | succ n ih => rw [sum_range_succ, mul_add, ih]; push_cast; ring

/-- `Σ_{x<δ} x = δ(δ−1)/2` over `ℝ`. -/
lemma sum_range_cast_id (δ : ℕ) :
    ∑ x ∈ range δ, (x : ℝ) = (δ : ℝ) * ((δ : ℝ) - 1) / 2 := by
  have h := two_mul_sum_range_cast_id δ
  rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)]
  linarith

/-- **Eq (23)**: the belief law is `2δ`-Lipschitz in `θ` for the total-variation
(unnormalised `ℓ¹`) distance. -/
theorem l1_lipschitz (θ θ' : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) (hθ' : θ' ∈ Icc (0 : ℝ) 1)
    (lam δ : ℕ) :
    ∑ x ∈ range (lam + δ + 1), |pmf θ lam δ x - pmf θ' lam δ x|
      ≤ 2 * (δ : ℝ) * |θ - θ'| := by
  rw [sum_range_succ, abs_pmf_sum_range_eq, pmf_of_eq rfl, pmf_of_eq rfl]
  have hterm : ∀ x ∈ range δ, |pmf θ lam δ x - pmf θ' lam δ x| ≤ |θ - θ'| := by
    intro x hx
    rw [pmf_of_lt (by simpa using hx), pmf_of_lt (by simpa using hx)]
    exact armTerm_lipschitz x hθ' hθ
  have hsum := sum_le_sum hterm
  have hconst : ∑ _x ∈ range δ, |θ - θ'| = (δ : ℝ) * |θ - θ'| := by
    rw [sum_const, card_range, nsmul_eq_mul]
  rw [hconst] at hsum
  have hatom := atomTerm_lipschitz δ hθ hθ'
  linarith

/-- **Eq (24)**: the same law is `(δ(δ−1)/2 + δ(λ+δ))`-Lipschitz for the first-moment
weighted distance.  Both constants are **tight** — see the "Lemma2" rows of
`scripts/numeric_check.py`. -/
theorem firstMoment_lipschitz (θ θ' : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hθ' : θ' ∈ Icc (0 : ℝ) 1) (lam δ : ℕ) :
    ∑ x ∈ range (lam + δ + 1), (x : ℝ) * |pmf θ lam δ x - pmf θ' lam δ x|
      ≤ ((δ : ℝ) * ((δ : ℝ) - 1) / 2 + (δ : ℝ) * ((lam : ℝ) + (δ : ℝ))) * |θ - θ'| := by
  rw [sum_range_succ, weighted_abs_pmf_sum_range_eq, pmf_of_eq rfl, pmf_of_eq rfl]
  have hterm : ∀ x ∈ range δ,
      (x : ℝ) * |pmf θ lam δ x - pmf θ' lam δ x| ≤ (x : ℝ) * |θ - θ'| := by
    intro x hx
    rw [pmf_of_lt (by simpa using hx), pmf_of_lt (by simpa using hx)]
    exact mul_le_mul_of_nonneg_left (armTerm_lipschitz x hθ' hθ) (Nat.cast_nonneg x)
  have hsum := sum_le_sum hterm
  have hconst : ∑ x ∈ range δ, (x : ℝ) * |θ - θ'|
      = ((δ : ℝ) * ((δ : ℝ) - 1) / 2) * |θ - θ'| := by
    rw [← sum_mul, sum_range_cast_id]
  rw [hconst] at hsum
  have hatom := mul_le_mul_of_nonneg_left (atomTerm_lipschitz δ hθ hθ') (Nat.cast_nonneg (lam + δ))
  push_cast at hatom ⊢
  linarith

end TSDPP
