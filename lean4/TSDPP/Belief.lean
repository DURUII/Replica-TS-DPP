/-
Copyright (c) 2026 TSDPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# R5, R6 — the belief state (paper Eq (15), Eq (16))

`TSDPP.pmf` is the exact law of an arm's state `X_i(t)` given the *record* `(λ, δ)`,
i.e. paper Eq (15):

  `P^θ_x = θ(1−θ)^x`  for `x = 0,…,δ−1`,   `P^θ_{λ+δ} = (1−θ)^δ`.

`TSDPP.pmf_mean` is paper Eq (16), the closed form of the belief state `X^b_i(t)`.
The mean is not restated as an expectation over a probability space: the paper's
`X^b_i(t)` *is* `Σ_x x·P^θ_x`, and that is what is proved here.
-/
import Mathlib

namespace TSDPP

open Finset

/-! ## Geometric-sum helpers

`θ · Σ_{x<δ} (1−θ)^x = 1 − (1−θ)^δ` is `geom_sum_mul_neg` in disguise and needs **no**
division, so it holds at `θ = 0` as well.  This is what keeps `pmf_sum_one` free of a
`θ ≠ 0` side condition (trap P-2 in `DESIGN.md`). -/

/-- `θ · Σ_{x<δ} (1−θ)^x = 1 − (1−θ)^δ`.  Valid for every real `θ`, including `0`. -/
lemma theta_mul_geom_sum (θ : ℝ) (δ : ℕ) :
    θ * ∑ x ∈ range δ, (1 - θ) ^ x = 1 - (1 - θ) ^ δ := by
  have h := geom_sum_mul_neg (1 - θ) δ
  have h' : (1 - (1 - θ)) = θ := by ring
  rw [h'] at h
  linear_combination h

/-- `Σ_{x<δ} x(1−θ)^x = (1 − (1−θ)^δ)/θ² − 1/θ − (δ−1)(1−θ)^δ/θ` for `θ ≠ 0`.
Proved by induction on `δ`.  Trap P-2: routing through `geom_sum_eq` would force a
`1−θ ≠ 1` case split that induction does not need. -/
lemma weighted_geom_sum (θ : ℝ) (hθ : θ ≠ 0) (δ : ℕ) :
    ∑ x ∈ range δ, (x : ℝ) * (1 - θ) ^ x
      = (1 - (1 - θ) ^ δ) / θ ^ 2 - 1 / θ - ((δ : ℝ) - 1) * (1 - θ) ^ δ / θ := by
  induction δ with
  | zero => simp only [sum_range_zero, Nat.cast_zero]; field_simp; ring
  | succ n ih =>
    rw [sum_range_succ, ih]
    have hθ2 : θ ^ 2 ≠ 0 := pow_ne_zero _ hθ
    field_simp
    push_cast
    ring

/-- The working form of `weighted_geom_sum`: multiplying by `θ` clears one factor,
leaving a single division by `θ`.  This is exactly the shape `pmf_mean` needs. -/
lemma theta_mul_weighted_geom_sum (θ : ℝ) (hθ : θ ≠ 0) (δ : ℕ) :
    θ * ∑ x ∈ range δ, (x : ℝ) * (1 - θ) ^ x
      = (1 - (1 - θ) ^ δ) / θ - 1 - ((δ : ℝ) - 1) * (1 - θ) ^ δ := by
  rw [weighted_geom_sum θ hθ δ]
  field_simp

/-! ## Eq (15): the law of `X_i(t)` given the record `(λ, δ)` -/

/-- Paper Eq (15).  `pmf θ λ δ x` is `P^θ_x = Pr(X_i(t) = x)`, where `λ = X_i(τ_i)` is the
state at the most recent selection of arm `i` and `δ = t − τ_i` is the number of slots
elapsed since.

The two branches are disjoint because `δ ≤ λ + δ` (trap P-5). -/
noncomputable def pmf (θ : ℝ) (lam δ x : ℕ) : ℝ :=
  if x < δ then θ * (1 - θ) ^ x else if x = lam + δ then (1 - θ) ^ δ else 0

lemma pmf_of_lt {θ : ℝ} {lam δ x : ℕ} (h : x < δ) : pmf θ lam δ x = θ * (1 - θ) ^ x := by
  rw [pmf, ite_eq_left h]

lemma pmf_of_eq {θ : ℝ} {lam δ x : ℕ} (h : x = lam + δ) : pmf θ lam δ x = (1 - θ) ^ δ := by
  have hlt : ¬ x < δ := by omega
  rw [pmf, ite_eq_right hlt, ite_eq_left h]

lemma pmf_of_other {θ : ℝ} {lam δ x : ℕ} (h1 : ¬ x < δ) (h2 : x ≠ lam + δ) :
    pmf θ lam δ x = 0 := by
  rw [pmf, ite_eq_right h1, ite_eq_right h2]

lemma pmf_nonneg {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (lam δ x : ℕ) :
    0 ≤ pmf θ lam δ x := by
  unfold pmf
  split_ifs with h1 h2
  · exact mul_nonneg hθ0 (pow_nonneg (by linarith) _)
  · exact pow_nonneg (by linarith) _
  · exact le_refl 0

/-- The support of `pmf θ λ δ` is contained in `{0,…,λ+δ}`. -/
lemma pmf_eq_zero_of_gt {θ : ℝ} {lam δ x : ℕ} (h : lam + δ < x) : pmf θ lam δ x = 0 :=
  pmf_of_other (by omega) (by omega)

/-- Restricting the sum to `range δ` loses nothing: every term with `δ ≤ x < λ+δ` vanishes.
This is the `x ∉ s₁ ⟹ f x = 0` obligation of `Finset.sum_subset`. -/
lemma pmf_sum_range_eq {θ : ℝ} {lam δ : ℕ} :
    ∑ x ∈ range (lam + δ), pmf θ lam δ x = ∑ x ∈ range δ, pmf θ lam δ x :=
  (sum_subset (s₁ := range δ) (s₂ := range (lam + δ)) (f := pmf θ lam δ)
    (fun x hx => by simp only [mem_range] at hx ⊢; omega)
    (fun x hx2 hx => by
      simp only [mem_range] at hx hx2
      exact pmf_of_other hx (by omega))).symm

lemma pmf_weighted_sum_range_eq {θ : ℝ} {lam δ : ℕ} :
    ∑ x ∈ range (lam + δ), (x : ℝ) * pmf θ lam δ x
      = ∑ x ∈ range δ, (x : ℝ) * pmf θ lam δ x :=
  (sum_subset (s₁ := range δ) (s₂ := range (lam + δ))
    (f := fun x => (x : ℝ) * pmf θ lam δ x)
    (fun x hx => by simp only [mem_range] at hx ⊢; omega)
    (fun x hx2 hx => by
      simp only [mem_range] at hx hx2
      rw [pmf_of_other hx (by omega), mul_zero])).symm

/-- Paper Eq (15) really is a probability mass function: it sums to `1` over the support
`{0,…,λ+δ}`, for every `θ`, including `θ = 0` and `θ = 1`. -/
theorem pmf_sum_one (θ : ℝ) (lam δ : ℕ) :
    ∑ x ∈ range (lam + δ + 1), pmf θ lam δ x = 1 := by
  rw [sum_range_succ, pmf_sum_range_eq, pmf_of_eq rfl]
  have : ∑ x ∈ range δ, pmf θ lam δ x = ∑ x ∈ range δ, θ * (1 - θ) ^ x :=
    sum_congr rfl fun x hx => pmf_of_lt (by simpa using hx)
  rw [this, ← mul_sum, theta_mul_geom_sum]
  ring

/-- Paper Eq (16): the belief state `X^b_i(t)` is the mean of the law Eq (15), and it
equals the closed form printed in the paper. -/
theorem pmf_mean (θ : ℝ) (hθ : θ ≠ 0) (lam δ : ℕ) :
    ∑ x ∈ range (lam + δ + 1), (x : ℝ) * pmf θ lam δ x
      = (1 - θ) / θ + (1 - θ) ^ δ * ((lam : ℝ) - (1 - θ) / θ) := by
  rw [sum_range_succ, pmf_weighted_sum_range_eq, pmf_of_eq rfl]
  have hcongr : ∑ x ∈ range δ, (x : ℝ) * pmf θ lam δ x
      = ∑ x ∈ range δ, (x : ℝ) * (θ * (1 - θ) ^ x) :=
    sum_congr rfl fun x hx => by rw [pmf_of_lt (by simpa using hx)]
  have hfac : ∑ x ∈ range δ, (x : ℝ) * (θ * (1 - θ) ^ x)
      = θ * ∑ x ∈ range δ, (x : ℝ) * (1 - θ) ^ x := by
    rw [mul_sum]
    exact sum_congr rfl fun x _ => by ring
  rw [hcongr, hfac, theta_mul_weighted_geom_sum θ hθ δ]
  push_cast
  field_simp
  ring

end TSDPP
