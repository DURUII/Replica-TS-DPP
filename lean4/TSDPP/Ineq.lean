/-
Copyright (c) 2026 TSDPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Elementary inequalities behind Lemma 2 (paper Eq (23), (25), (26))

The paper bounds `sup_{[0,1]} |f'|` for `f(t) = t(1−t)^x` by `1` (its Eq (25)).  Rather
than estimating that derivative directly, we reduce it to two Bernoulli-inequality
corollaries:

* `aux1`: `u^x + x·u^{x−1}(1−u) ≤ 1`        — the positive part of `f'`
* `aux2`: `(x+1)·u^x − x·u^{x−1} ≤ 1`       — the absolute value of the negative part

`aux1` is proved by the substitution `a = (1−u)/u`, which is exactly the change of
variable under which `u^x(1+a)^x = (u(1+a))^x = 1`, turning it into Bernoulli's
inequality `1 + n·a ≤ (1+a)^n`.

`aux2` is **not** proved that way.  Clearing denominators in `aux2` produces the
statement `1 − (k+1)c ≤ (1+c)^{k+1}` for `c = (1−u)/u`, which is *false* for `c < 0`
(i.e. for `u > 1/2`): Bernoulli gives only `(1+c)^{k+1} ≥ 1 + (k+1)c`, and the two
sides point the wrong way when `c < 0`.  The direct route instead rewrites the
expression as `u^{k+1} − (k+1)u^k(1−u)`, whose subtracted term is non-negative, so it
is dominated by `u^{k+1} ≤ 1`.  See trap P-9 in `DESIGN.md`.

Both constants are **tight** — the numeric falsifier (`scripts/numeric_check.py`,
row "Eq(25)") confirms `sup|f'| = 1`.
-/
import Mathlib

namespace TSDPP

/-- Bernoulli in the `k+1` form, which is the index shape the proofs below need.
`u^(k+1) + (k+1)·u^k·(1−u) ≤ 1` for `u ∈ (0,1]`. -/
lemma pow_add_weighted_le_one {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) (k : ℕ) :
    u ^ (k + 1) + ((k : ℝ) + 1) * u ^ k * (1 - u) ≤ 1 := by
  set c : ℝ := (1 - u) / u with hc
  have hu_ne : u ≠ 0 := ne_of_gt hu0
  have hcu : u * (1 + c) = 1 := by rw [hc]; field_simp; ring
  have hc2 : (-2 : ℝ) ≤ c := by
    have : 0 ≤ (1 - u) / u := div_nonneg (by linarith) hu0.le
    rw [hc]; linarith
  have hbern : 1 + ((k : ℝ) + 1) * c ≤ (1 + c) ^ (k + 1) := by
    have h := one_add_mul_le_pow (a := c) hc2 (k + 1)
    push_cast at h
    linarith [h]
  have hux : 0 ≤ u ^ (k + 1) := pow_nonneg hu0.le _
  have key : u ^ (k + 1) * (1 + ((k : ℝ) + 1) * c) ≤ 1 := by
    calc u ^ (k + 1) * (1 + ((k : ℝ) + 1) * c)
        ≤ u ^ (k + 1) * (1 + c) ^ (k + 1) := mul_le_mul_of_nonneg_left hbern hux
      _ = 1 := by rw [← mul_pow, hcu, one_pow]
  have hux' : u ^ (k + 1) = u * u ^ k := pow_succ' u k
  have expand : u ^ (k + 1) * (1 + ((k : ℝ) + 1) * c)
      = u ^ (k + 1) + ((k : ℝ) + 1) * u ^ k * (1 - u) := by
    rw [hux', hc]
    field_simp
  linarith [key, expand.le, expand.ge]

/-- `u^x + x·u^{x−1}(1−u) ≤ 1` for `u ∈ (0,1]`.  This is `aux1` in the general index.

Trap P-8: `u^x` and `u^{x−1}` are *distinct atoms* to `ring`, so the general-index
statement cannot be proved by `ring` manipulation of the shift; it is derived from the
`k+1` statement by casing on `x`, where `pow_succ'` and `Nat.add_sub_cancel` do the
index shift. -/
lemma pow_add_weighted_le_one' {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) (x : ℕ) :
    u ^ x + (x : ℝ) * u ^ (x - 1) * (1 - u) ≤ 1 := by
  rcases x with _ | k
  · simp
  · simpa [Nat.cast_add, Nat.add_sub_cancel] using pow_add_weighted_le_one hu0 hu1 k

/-- `(k+2)·u^{k+1} − (k+1)·u^k ≤ 1` for `u ∈ (0,1]`; the `k+1` index shape of `aux2`.

The subtraction is *not* an obstruction: writing the expression as
`u^{k+1} − (k+1)·u^k·(1−u)`, the subtracted term is non-negative because `u ≤ 1`, so
the whole thing is bounded by `u^{k+1} ≤ 1`.  See trap P-9 for why the denominator-
clearing route (which is correct for `aux1`) breaks here. -/
lemma succ_mul_pow_sub_le_one {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) (k : ℕ) :
    ((k : ℝ) + 2) * u ^ (k + 1) - ((k : ℝ) + 1) * u ^ k ≤ 1 := by
  have hux : u ^ (k + 1) = u * u ^ k := pow_succ' u k
  have hrewrite : ((k : ℝ) + 2) * u ^ (k + 1) - ((k : ℝ) + 1) * u ^ k
      = u ^ (k + 1) - ((k : ℝ) + 1) * u ^ k * (1 - u) := by
    rw [hux]; ring
  rw [hrewrite]
  have hsub : 0 ≤ ((k : ℝ) + 1) * u ^ k * (1 - u) := by
    have h1 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
    have h2 : 0 ≤ u ^ k := pow_nonneg hu0.le k
    have h3 : 0 ≤ 1 - u := by linarith
    exact mul_nonneg (mul_nonneg h1 h2) h3
  have hpow : u ^ (k + 1) ≤ 1 := by
    calc u ^ (k + 1) ≤ 1 ^ (k + 1) := pow_le_pow_left₀ hu0.le hu1 _
      _ = 1 := one_pow _
  linarith

/-- The *negative* half of `sup|f'| ≤ 1`: `(k+1)·u^k − (k+2)·u^{k+1} ≤ 1`, i.e. the
negation of `succ_mul_pow_sub_le_one` is bounded by `1`.

This is `aux1` with the `u^{k+1}` term absorbed: `aux1` reads
`u^{k+1} + (k+1)u^k(1−u) ≤ 1`, which expands to `(k+1)u^k − k·u^{k+1} ≤ 1`; dropping
the non-negative `u^{k+1}` down to `−(k+2)u^{k+1}` only weakens the left-hand side. -/
lemma mul_pow_sub_succ_mul_pow_le_one {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) (k : ℕ) :
    ((k : ℝ) + 1) * u ^ k - ((k : ℝ) + 2) * u ^ (k + 1) ≤ 1 := by
  have h := pow_add_weighted_le_one hu0 hu1 k
  have hux : u ^ (k + 1) = u * u ^ k := pow_succ' u k
  rw [hux] at h ⊢
  have hnn : 0 ≤ u * u ^ k := by positivity
  nlinarith [h, hnn]

/-- `(x+1)·u^x − x·u^{x−1} ≤ 1` for `u ∈ (0,1]`; `aux2` in the general index. -/
lemma succ_mul_pow_sub_le_one' {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) (x : ℕ) :
    ((x : ℝ) + 1) * u ^ x - (x : ℝ) * u ^ (x - 1) ≤ 1 := by
  rcases x with _ | k
  · simp
  · have hgoal : ((k : ℝ) + 1 + 1) = (k : ℝ) + 2 := by ring
    simpa [Nat.cast_add, Nat.add_sub_cancel, hgoal] using succ_mul_pow_sub_le_one hu0 hu1 k

end TSDPP
