/-
Copyright (c) 2026 TSDPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Asymp — Theorem 2's `O(·)`, formalized rather than left as notation

Theorem 2 of the paper is stated as

  `BR(T) = O( √(L³ · T · log T) )`,  `T = m·L`.

`Theorem2.theorem3_rate` proves the concrete bound `|BR| ≤ c·L·√(L³·T·log T/η)` with an explicit,
`T`-free constant `c`.  What was missing is the passage to the asymptotic statement itself.  This
module supplies it in `Asymptotics`' own language.

## The convention, which is the whole of GAP-4

`O(·)` presupposes a *filter*: which variable tends to infinity, and what happens to the others.
The paper never says.  It writes `L³·T·log T` with `T = m·L`, so `L` appears in the rate — but it
also calls `L` the episode length and treats it as a constant elsewhere.  The two readings give
different classes:

* **`L` fixed** (the paper's operative reading — `L` is a design parameter held constant while the
  horizon `T` grows): `√(L³·T·log T) = √(L³)·√(T·log T)`, so the rate is `Θ(√(T·log T))`.
  This is `sqrt_L3TlogT_isTheta` below.
* **`L` growing with `T`**: a different claim, not formalized here.

This module takes the first reading and makes it explicit rather than implicit.  That is a
modelling decision, stated as such — not a mathematical gap.  `FIDELITY.md` §4 records it.

## What is proved

* `sqrt_L3TlogT_isTheta` — for fixed `L > 0`, `√(L³·T·log T) =Θ[atTop] √(T·log T)`.
* `bound_isBigO_sqrt_log` — the `theorem3_rate` right-hand side is `O(√(T·log T))`, with the
  constant exhibited as `c·L·√(L³/η)`.
-/
import Mathlib
import TSDPP.Theorem2

namespace TSDPP

open Filter Asymptotics

/-- **The `L³` is a constant factor.**  For fixed `L > 0`, pulling `L³` out of the radical turns
`√(L³·T·log T)` into `√(L³)·√(T·log T)`; since `√(L³)` is a positive constant, the two are
`Θ`-equivalent as `T → ∞`.

This is the step that makes the paper's `√(L³T log T)` and the headline `√(T log T)` the same
rate, and it is exactly where GAP-4's convention is spent: it holds for *fixed* `L`. -/
theorem sqrt_L3TlogT_isTheta {L : ℝ} (hL : 0 < L) :
    (fun T : ℝ => Real.sqrt (L ^ 3 * T * Real.log T))
      =Θ[atTop] (fun T : ℝ => Real.sqrt (T * Real.log T)) := by
  show (fun T : ℝ => Real.sqrt (L ^ 3 * T * Real.log T))
      =Θ[atTop] (fun T : ℝ => Real.sqrt (T * Real.log T))
  have hL3 : 0 < L ^ 3 := by positivity
  -- `√(L³·T·log T) = √(L³) · √(T·log T)` once `T·log T ≥ 0`, which holds for `T ≥ 1`.
  have hfac : ∀ T : ℝ, 1 ≤ T →
      Real.sqrt (L ^ 3 * T * Real.log T) = Real.sqrt (L ^ 3) * Real.sqrt (T * Real.log T) := by
    intro T hT
    have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
    have hT0 : 0 ≤ T := by linarith
    have hTlog : 0 ≤ T * Real.log T := mul_nonneg hT0 hlogT
    rw [show L ^ 3 * T * Real.log T = L ^ 3 * (T * Real.log T) by ring,
      Real.sqrt_mul hL3.le]
  have hpos : 0 < Real.sqrt (L ^ 3) := Real.sqrt_pos.mpr hL3
  constructor
  · -- `√(L³T log T) =O √(T log T)`: the constant is `√(L³)`.
    refine IsBigO.of_bound (Real.sqrt (L ^ 3)) ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    rw [hfac T hT]
    -- `simp only` rewrites *every* occurrence; `rw` would stop at the first `|·|`.
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact le_refl _
  · -- Conversely `√(T log T) ≤ (√(L³))⁻¹ · √(L³T log T)`: the constant is `(√(L³))⁻¹`, and the
    -- identity `(√L³)⁻¹ · √L³ = 1` is what makes the `≤` an equality.
    refine IsBigO.of_bound ((Real.sqrt (L ^ 3))⁻¹) ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    rw [hfac T hT]
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]

/-- **Theorem 2's rate, as `O(·)`.**  The right-hand side of `Theorem2.theorem3_rate`,
`c·L·√(L³·T·log T/η)`, is `O(√(T·log T))` as `T → ∞` with `L`, `η`, `c` held fixed.

Combined with `theorem3_rate` this is the paper's `BR(T) = O(√(T log T))` under the fixed-`L`
reading; under the growing-`L` reading the paper's printed factor `√(L³·T·log T)` is
`L^{3/2}√(T log T)`, while this module's bound carries the further factor `L` and is
`Θ(L^{5/2}√(T log T))` at fixed `c`, `η`.  The constant exhibited below is `c·L·√(L³/η)`, precisely
the factor that would have to be re-examined if `L` grew. -/
theorem bound_isBigO_sqrt_log {L η c : ℝ} (hL : 0 < L) (hη : 0 < η) :
    (fun T : ℝ => c * L * Real.sqrt (L ^ 3 * T * Real.log T / η))
      =O[atTop] (fun T : ℝ => Real.sqrt (T * Real.log T)) := by
  show (fun T : ℝ => c * L * Real.sqrt (L ^ 3 * T * Real.log T / η))
      =O[atTop] (fun T : ℝ => Real.sqrt (T * Real.log T))
  have hL3η : 0 ≤ L ^ 3 / η := by positivity
  have hfac : ∀ T : ℝ, 1 ≤ T →
      Real.sqrt (L ^ 3 * T * Real.log T / η)
        = Real.sqrt (L ^ 3 / η) * Real.sqrt (T * Real.log T) := by
    intro T hT
    have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
    have hT0 : 0 ≤ T := by linarith
    rw [show L ^ 3 * T * Real.log T / η = (L ^ 3 / η) * (T * Real.log T) by ring,
      Real.sqrt_mul hL3η]
  refine IsBigO.of_bound (|c * L * Real.sqrt (L ^ 3 / η)|) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  rw [hfac T hT, show c * L * (Real.sqrt (L ^ 3 / η) * Real.sqrt (T * Real.log T))
      = (c * L * Real.sqrt (L ^ 3 / η)) * Real.sqrt (T * Real.log T) by ring]
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact le_refl _

/-- **The `T → ∞` limit is the `m → ∞` limit.**  Since `T = m·L` with `L > 0` fixed, letting the
number of *episodes* grow is the same filter as letting the horizon grow.  This composes
`bound_isBigO_sqrt_log` with `T = fun m => m·L` (`Asymptotics.IsBigO.comp_tendsto`), which is the
form in which `theorem3_rate` delivers its bound.

Note the composite still reads `O(√(T log T))` with `T = m·L` written out, rather than `√(m log m)`:
the two differ by the fixed factor `√(L(log m + log L)/log m) → √L`, which is a constant for fixed
`L`.  Keeping `T` visible avoids silently burying that step. -/
theorem bound_isBigO_in_episodes {L η c : ℝ} (hL : 0 < L) (hη : 0 < η) :
    (fun m : ℝ => c * L * Real.sqrt (L ^ 3 * (m * L) * Real.log (m * L) / η))
      =O[atTop] (fun m : ℝ => Real.sqrt ((m * L) * Real.log (m * L))) := by
  show (fun m : ℝ => c * L * Real.sqrt (L ^ 3 * (m * L) * Real.log (m * L) / η))
      =O[atTop] (fun m : ℝ => Real.sqrt ((m * L) * Real.log (m * L)))
  -- `T ↦ T` composed with `m ↦ m·L` is the identity on the `T`-side; `m ↦ m·L` tends to `atTop`
  -- because `L > 0`.
  have hk : Tendsto (fun m : ℝ => m * L) atTop atTop :=
    tendsto_id.atTop_mul_const' hL
  exact (bound_isBigO_sqrt_log (L := L) (η := η) (c := c) hL hη).comp_tendsto hk

end TSDPP
