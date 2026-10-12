/-
Copyright (c) 2026 TSDPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Probe: algebraic identities for the exact Chernoff optimisers of the Beta tails, in the
α-cleared form (no nested `β/α` divisions) plus the rpow bookkeeping.
Not part of the build; Scratch/ is excluded from `scripts/scan_forbidden.py`'s stem scan.
-/
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TSDPP

/-- `x^β = (x^(β/α))^α`, the `ρ`-parametrisation of the Gamma exponent. -/
private lemma rpow_beta_eq {α β : ℝ} (hα : (α : ℝ) ≠ 0) {x : ℝ} (hx : 0 ≤ x) :
    x ^ β = (x ^ (β / α)) ^ α := by
  rw [← Real.rpow_mul hx (β / α) α, show β / α * α = β by field_simp]

example {α β δ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hδ : 0 < δ) (hδρ : δ < β / α) :
    (δ * (α + β) / ((1 + δ) * (β - δ * α))) * (1 - α / (α + β) * (1 + δ))
      = δ / (1 + δ) := by
  have h1 : β - δ * α ≠ 0 := by
    have := (lt_div_iff₀ hα).1 hδρ
    linarith
  have h2 : α + β ≠ 0 := by positivity
  have h3 : 1 + δ ≠ 0 := by positivity
  field_simp
  ring

example {α β δ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hδ : 0 < δ) (hδρ : δ < β / α) :
    (δ * (α + β) / ((1 + δ) * (β - δ * α))) * (α / (α + β) * (1 + δ))
      = δ * α / (β - δ * α) := by
  have h1 : β - δ * α ≠ 0 := by
    have := (lt_div_iff₀ hα).1 hδρ
    linarith
  have h2 : α + β ≠ 0 := by positivity
  have h3 : 1 + δ ≠ 0 := by positivity
  field_simp

example {α β δ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ((1 - δ) * (α + β) / (δ * (α + β - δ * α))) * (α / (α + β) * δ)
      = α * (1 - δ) / (α + β - δ * α) := by
  have h1 : δ ≠ 0 := ne_of_gt hδ
  have h2 : α + β ≠ 0 := by positivity
  have h3 : α + β - δ * α ≠ 0 := by
    have : δ * α < 1 * α := by nlinarith
    linarith
  field_simp

example {α β δ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 + ((1 - δ) * (α + β) / (δ * (α + β - δ * α))) * (1 - α / (α + β) * δ)
      = δ⁻¹ := by
  have h1 : δ ≠ 0 := ne_of_gt hδ
  have h2 : α + β ≠ 0 := by positivity
  have h3 : α + β - δ * α ≠ 0 := by
    have : δ * α < 1 * α := by nlinarith
    linarith
  field_simp
  ring

end TSDPP
