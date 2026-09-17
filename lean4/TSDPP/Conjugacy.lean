/-
Copyright (c) 2026 TSDPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.Distributions.Beta
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Beta–Bernoulli conjugacy (card R7 = Theorem 1 of the paper)

The paper's Eq (21)–(22): with a `Beta(α, β)` prior on the event probability `θ`,
observing a Bernoulli/geometric record with `A` occurrences and `B` non-occurrences
updates the posterior to `Beta(α + A, β + B)`.

This file formalises the analytic core of that statement, namely the *pointwise*
density identity

`betaPDFReal (α + A) (β + B) x = (beta α β / beta (α+A) (β+B)) * (x^A * (1-x)^B)
  * betaPDFReal α β x`

together with its integrated (`lintegral`) form, which says that the unnormalised
posterior `x ↦ x^A (1-x)^B * betaPDFReal α β x` has total mass
`beta (α+A) (β+B) / beta α β`. Dividing the pointwise identity by
`betaPDFReal α β x` recovers the textbook Bayes-update statement.

No axioms, no `sorry`, no `native_decide`, no `unsafe`, no floats.
-/

@[expose] public section

open scoped ENNReal NNReal

namespace TSDPP

/-! ## (a) The pointwise density-level conjugacy identity -/

/-- **Beta–Bernoulli conjugacy, pointwise form (restricted to `0 < x < 1`).**

For `α, β > 0`, `A B : ℕ` and `0 < x < 1`, the `Beta(α+A, β+B)` density at `x`
equals the normalising ratio `beta α β / beta (α+A) (β+B)` times the likelihood
`x^A (1-x)^B` times the `Beta(α, β)` density at `x`. This is the analytic content
of Eq (21)–(22) of the paper. -/
theorem betaPDFReal_conj (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (A B : ℕ) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    ProbabilityTheory.betaPDFReal (α + A) (β + B) x
      = (ProbabilityTheory.beta α β / ProbabilityTheory.beta (α + A) (β + B))
        * (x ^ A * (1 - x) ^ B) * ProbabilityTheory.betaPDFReal α β x := by
  have hA : (0 : ℝ) < α + A := add_pos_of_pos_of_nonneg hα (Nat.cast_nonneg A)
  have hB : (0 : ℝ) < β + B := add_pos_of_pos_of_nonneg hβ (Nat.cast_nonneg B)
  have hx1' : (0 : ℝ) < 1 - x := by linarith
  have h1 : ProbabilityTheory.beta (α + A) (β + B) ≠ 0 :=
    ne_of_gt (ProbabilityTheory.beta_pos hA hB)
  have h2 : ProbabilityTheory.beta α β ≠ 0 := ne_of_gt (ProbabilityTheory.beta_pos hα hβ)
  show (if 0 < x ∧ x < 1 then
      (1 / ProbabilityTheory.beta (α + A) (β + B)) * x ^ (α + A - 1) * (1 - x) ^ (β + B - 1)
    else 0)
    = (ProbabilityTheory.beta α β / ProbabilityTheory.beta (α + A) (β + B))
        * (x ^ A * (1 - x) ^ B)
        * (if 0 < x ∧ x < 1 then
            (1 / ProbabilityTheory.beta α β) * x ^ (α - 1) * (1 - x) ^ (β - 1)
          else 0)
  rw [ite_eq_left ⟨hx0, hx1⟩, ite_eq_left ⟨hx0, hx1⟩]
  show (1 / ProbabilityTheory.beta (α + A) (β + B)) * x ^ (α + A - 1) * (1 - x) ^ (β + B - 1)
    = (ProbabilityTheory.beta α β / ProbabilityTheory.beta (α + A) (β + B))
        * (x ^ A * (1 - x) ^ B)
        * ((1 / ProbabilityTheory.beta α β) * x ^ (α - 1) * (1 - x) ^ (β - 1))
  rw [show α + (A : ℝ) - 1 = (α - 1) + (A : ℝ) by ring,
      show β + (B : ℝ) - 1 = (β - 1) + (B : ℝ) by ring]
  rw [Real.rpow_add hx0, Real.rpow_add hx1']
  rw [← Real.rpow_natCast x A, ← Real.rpow_natCast (1 - x) B]
  field_simp

/-- **Beta–Bernoulli conjugacy, unconditional pointwise form.**

The restricted identity `betaPDFReal_conj` in fact holds at *every* real `x`:
outside `(0,1)` both `betaPDFReal`'s vanish, so the right-hand side is `0` as well.
This unconditional form is what makes the `lintegral` statement `lintegral_conj`
tractable. -/
theorem betaPDFReal_conj_all (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (A B : ℕ) (x : ℝ) :
    ProbabilityTheory.betaPDFReal (α + A) (β + B) x
      = (ProbabilityTheory.beta α β / ProbabilityTheory.beta (α + A) (β + B))
        * (x ^ A * (1 - x) ^ B) * ProbabilityTheory.betaPDFReal α β x := by
  by_cases h : 0 < x ∧ x < 1
  · exact betaPDFReal_conj α β hα hβ A B h.1 h.2
  · simp only [ProbabilityTheory.betaPDFReal, ite_eq_right h, mul_zero]

/-- **Beta–Bernoulli conjugacy in Bayes-ratio form.**

Dividing `betaPDFReal_conj` by the prior density `betaPDFReal α β x` (strictly positive
for `0 < x < 1`) exhibits the posterior density as the prior density times the
likelihood `x^A (1-x)^B` times the normalising constant `beta α β / beta (α+A) (β+B)`.
This is the literal "posterior ∝ prior × likelihood" reading of Eq (21)–(22) of the
paper; the integrated form `lintegral_conj` below is the statement that additionally
pins down the normalising constant. -/
theorem betaPDFReal_conj_ratio (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (A B : ℕ) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    ProbabilityTheory.betaPDFReal (α + A) (β + B) x / ProbabilityTheory.betaPDFReal α β x
      = (ProbabilityTheory.beta α β / ProbabilityTheory.beta (α + A) (β + B))
        * (x ^ A * (1 - x) ^ B) := by
  rw [betaPDFReal_conj α β hα hβ A B hx0 hx1]
  field_simp [ne_of_gt (ProbabilityTheory.betaPDFReal_pos hx0 hx1 hα hβ)]

/-- The unnormalised posterior weight `x^A (1-x)^B * betaPDFReal α β x` is nonnegative,
because `betaPDFReal` vanishes off `(0,1)` and on `(0,1)` both factors are nonnegative. -/
theorem conjWeight_nonneg (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (A B : ℕ) (x : ℝ) :
    0 ≤ (x ^ A * (1 - x) ^ B) * ProbabilityTheory.betaPDFReal α β x := by
  by_cases h : 0 < x ∧ x < 1
  · exact mul_nonneg (mul_nonneg (pow_nonneg h.1.le A) (pow_nonneg (by linarith) B))
      (le_of_lt (ProbabilityTheory.betaPDFReal_pos h.1 h.2 hα hβ))
  · simp only [ProbabilityTheory.betaPDFReal, ite_eq_right h, mul_zero, le_refl]

/-- **Beta–Bernoulli conjugacy, integrated form.**

The unnormalised posterior `x ↦ x^A (1-x)^B * betaPDFReal α β x` has total mass
`beta (α+A) (β+B) / beta α β`. Equivalently: the normalised `Beta(α+A, β+B)`
density is obtained from `Beta(α, β)` by multiplying by the likelihood
`x^A (1-x)^B` and dividing by its total mass. -/
theorem lintegral_conj (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (A B : ℕ) :
    ∫⁻ x, ENNReal.ofReal ((x ^ A * (1 - x) ^ B) * ProbabilityTheory.betaPDFReal α β x)
      = ENNReal.ofReal (ProbabilityTheory.beta (α + A) (β + B) / ProbabilityTheory.beta α β) := by
  have hA : (0 : ℝ) < α + A := add_pos_of_pos_of_nonneg hα (Nat.cast_nonneg A)
  have hB : (0 : ℝ) < β + B := add_pos_of_pos_of_nonneg hβ (Nat.cast_nonneg B)
  have hc : (0 : ℝ) < ProbabilityTheory.beta (α + A) (β + B) / ProbabilityTheory.beta α β :=
    div_pos (ProbabilityTheory.beta_pos hA hB) (ProbabilityTheory.beta_pos hα hβ)
  have hcinv : (0 : ℝ) < ProbabilityTheory.beta α β / ProbabilityTheory.beta (α + A) (β + B) :=
    div_pos (ProbabilityTheory.beta_pos hα hβ) (ProbabilityTheory.beta_pos hA hB)
  have hbn : ProbabilityTheory.beta (α + A) (β + B) ≠ 0 := ne_of_gt (ProbabilityTheory.beta_pos hA hB)
  have hbo : ProbabilityTheory.beta α β ≠ 0 := ne_of_gt (ProbabilityTheory.beta_pos hα hβ)
  have hpt : ∀ x, ENNReal.ofReal ((x ^ A * (1 - x) ^ B) * ProbabilityTheory.betaPDFReal α β x)
      = ENNReal.ofReal (ProbabilityTheory.beta (α + A) (β + B) / ProbabilityTheory.beta α β)
        * ProbabilityTheory.betaPDF (α + A) (β + B) x := by
    intro x
    by_cases h : 0 < x ∧ x < 1
    · have h1 : ProbabilityTheory.betaPDF (α + A) (β + B) x
          = ENNReal.ofReal (ProbabilityTheory.beta α β / ProbabilityTheory.beta (α + A) (β + B))
            * ENNReal.ofReal
                ((x ^ A * (1 - x) ^ B) * ProbabilityTheory.betaPDFReal α β x) := by
        rw [ProbabilityTheory.betaPDF,
          betaPDFReal_conj α β hα hβ A B h.1 h.2, mul_assoc,
          ENNReal.ofReal_mul hcinv.le]
      · rw [h1, ← mul_assoc, ← ENNReal.ofReal_mul hc.le,
          show ProbabilityTheory.beta (α + A) (β + B) / ProbabilityTheory.beta α β
              * (ProbabilityTheory.beta α β / ProbabilityTheory.beta (α + A) (β + B)) = 1 by
            field_simp [hbn, hbo],
          ENNReal.ofReal_one, one_mul]
    · simp only [ProbabilityTheory.betaPDFReal, ite_eq_right h, mul_zero, ENNReal.ofReal_zero,
        ProbabilityTheory.betaPDF, mul_zero]
  calc ∫⁻ x, ENNReal.ofReal ((x ^ A * (1 - x) ^ B) * ProbabilityTheory.betaPDFReal α β x)
      = ∫⁻ x, ENNReal.ofReal (ProbabilityTheory.beta (α + A) (β + B) / ProbabilityTheory.beta α β)
          * ProbabilityTheory.betaPDF (α + A) (β + B) x := MeasureTheory.lintegral_congr hpt
    _ = ENNReal.ofReal (ProbabilityTheory.beta (α + A) (β + B) / ProbabilityTheory.beta α β)
          * ∫⁻ x, ProbabilityTheory.betaPDF (α + A) (β + B) x :=
        MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (ProbabilityTheory.beta (α + A) (β + B) / ProbabilityTheory.beta α β) := by
        rw [ProbabilityTheory.lintegral_betaPDF_eq_one hA hB, mul_one]

end TSDPP
