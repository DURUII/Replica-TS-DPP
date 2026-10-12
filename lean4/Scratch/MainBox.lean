/-
Copyright (c) 2026 TSDPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

-- Skeleton of the machine-checked refutation of the registered Lemma 5 target.
-- The two Beta(1,B) tail facts are taken here as hypotheses (`hIci`, `hIic`);
-- `TSDPP/BetaOneCDF.lean` is the file that discharges them.

namespace TSDPP

/-- **Box containment.**  If `s ≤ t - u` and `0 ≤ s`, the rectangle
`{X ≥ t} × {Y ≤ u}` is contained in `{|X - Y| ≥ s}`.  The only point to check is
`p₁ - p₂ ≥ t - u ≥ s ≥ 0`, so `|p₁ - p₂| = p₁ - p₂`. -/
theorem prod_Ici_prod_Iic_le_abs_sub {μ : Measure ℝ} {s t u : ℝ} (hs : 0 ≤ s)
    (h : s ≤ t - u) :
    (μ.prod μ) (Set.Ici t ×ˢ Set.Iic u) ≤ (μ.prod μ) {p : ℝ × ℝ | s ≤ |p.1 - p.2|} := by
  refine measure_mono ?_
  rintro ⟨p1, p2⟩ hmem
  rw [Set.mem_prod] at hmem
  obtain ⟨h1, h2⟩ := hmem
  have h1' : t ≤ p1 := h1
  have h2' : p2 ≤ u := h2
  have h3 : s ≤ p1 - p2 := by linarith
  have h4 : 0 ≤ p1 - p2 := le_trans hs h3
  simp only [Set.mem_ofPred_eq]
  show s ≤ |p1 - p2|
  rw [abs_of_nonneg h4]
  exact h3

end TSDPP

namespace TSDPP

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **The general form.**  For *any* constant `c` whose exponent at `r = 14` is beaten by the
certificate `LB = (86/101)^100 · (1 − (100/101)^100)`, the bound `2·exp(−c·α·r²)` is **false** on the
registered range `r ≥ 1`.  `LB = 6.5651904266542612343e−8`, so the hypothesis is `c > 0.0879…`:
**no constant above `0.08792` survives on `r ≥ 1`**, and in particular neither the artifact's
`11/100` nor the paper's own `1/8` does.

The two Beta(1,100) tail facts (`hIci`, `hIic`) are the only analytic inputs; `harith` is the pure
arithmetic residual.  Everything else is measure theory and `ring`. -/
theorem lemma5_range_ge_one_is_false
    (hIci : betaMeasure (1 : ℝ) ((100 : ℕ) : ℝ) (Set.Ici (15 / 101))
              = ENNReal.ofReal (((86 : ℝ) / 101) ^ 100))
    (hIic : betaMeasure (1 : ℝ) ((100 : ℕ) : ℝ) (Set.Iic (1 / 101))
              = ENNReal.ofReal (1 - ((100 : ℝ) / 101) ^ 100))
    (c : ℝ)
    (harith : 2 * Real.exp (-196 * c)
                < ((86 : ℝ) / 101) ^ 100 * (1 - ((100 : ℝ) / 101) ^ 100)) :
    ¬ (∀ (α β r : ℝ), 0 < α → 0 < β → 1 ≤ r →
        ((betaMeasure α β).prod (betaMeasure α β))
          {p : ℝ × ℝ | r * (α / (α + β)) ≤ |p.1 - p.2|}
          ≤ ENNReal.ofReal (2 * Real.exp (-c * α * r ^ 2))) := by
  intro h
  have h0 := h 1 100 14 (by norm_num) (by norm_num) (by norm_num)
  have harg : (14 : ℝ) * (1 / (1 + 100)) = 14 / 101 := by norm_num
  rw [harg] at h0
  have hexp : -(c) * 1 * (14 : ℝ) ^ 2 = -196 * c := by ring
  rw [hexp] at h0
  have hbox := prod_Ici_prod_Iic_le_abs_sub
    (μ := betaMeasure (1 : ℝ) ((100 : ℕ) : ℝ)) (s := 14 / 101) (t := 15 / 101)
    (u := 1 / 101) (by norm_num) (by norm_num)
  haveI : IsProbabilityMeasure (betaMeasure (1 : ℝ) ((100 : ℕ) : ℝ)) :=
    isProbabilityMeasureBeta (by norm_num) (by norm_num)
  have hprod : ((betaMeasure (1 : ℝ) ((100 : ℕ) : ℝ)).prod
        (betaMeasure (1 : ℝ) ((100 : ℕ) : ℝ)))
      (Set.Ici (15 / 101) ×ˢ Set.Iic (1 / 101))
      = ENNReal.ofReal (((86 : ℝ) / 101) ^ 100 * (1 - ((100 : ℝ) / 101) ^ 100)) := by
    rw [Measure.prod_prod, hIci, hIic, ← ENNReal.ofReal_mul (by positivity)]
  have hlt : ENNReal.ofReal (2 * Real.exp (-196 * c))
      < ((betaMeasure (1 : ℝ) ((100 : ℕ) : ℝ)).prod (betaMeasure (1 : ℝ) ((100 : ℕ) : ℝ)))
          {p : ℝ × ℝ | 14 / 101 ≤ |p.1 - p.2|} := by
    refine lt_of_lt_of_le ?_ hbox
    rw [hprod]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr harith
  exact (not_le_of_gt hlt) h0

/-- **The artifact's registered target is FALSE**: the constant `c₀ = 11/100` does not survive on
`r ≥ 1`. -/
theorem lemma5_as_registered_is_false
    (hIci : betaMeasure (1 : ℝ) ((100 : ℕ) : ℝ) (Set.Ici (15 / 101))
              = ENNReal.ofReal (((86 : ℝ) / 101) ^ 100))
    (hIic : betaMeasure (1 : ℝ) ((100 : ℕ) : ℝ) (Set.Iic (1 / 101))
              = ENNReal.ofReal (1 - ((100 : ℝ) / 101) ^ 100))
    (harith : 2 * Real.exp (-(539 / 25 : ℝ))
                < ((86 : ℝ) / 101) ^ 100 * (1 - ((100 : ℝ) / 101) ^ 100)) :
    ¬ (∀ (α β r : ℝ), 0 < α → 0 < β → 1 ≤ r →
        ((betaMeasure α β).prod (betaMeasure α β))
          {p : ℝ × ℝ | r * (α / (α + β)) ≤ |p.1 - p.2|}
          ≤ ENNReal.ofReal (2 * Real.exp (-(11 / 100) * α * r ^ 2))) := by
  refine lemma5_range_ge_one_is_false hIci hIic (11 / 100) ?_
  have h : -(196 : ℝ) * (11 / 100) = -(539 / 25) := by norm_num
  rwa [h]

/-- **The paper's own constant `1/8` is FALSE on the paper's own range `r ≥ 1`** (trap P-67, made
machine-checked).  This is the statement that does *not* depend on the artifact's transposed
constant: whatever one thinks of `11/100`, the lemma with `1/8` — the constant printed on p. 9 — is
false on the range Eq (33) applies it to.

Derived from the same certificate, since `1/8 > 11/100` makes the required right-hand side smaller:
`exp(−49/2) < exp(−539/25)` because `49/2 = 24.5 > 21.56`. -/
theorem paper_lemma5_range_ge_one_is_false
    (hIci : betaMeasure (1 : ℝ) ((100 : ℕ) : ℝ) (Set.Ici (15 / 101))
              = ENNReal.ofReal (((86 : ℝ) / 101) ^ 100))
    (hIic : betaMeasure (1 : ℝ) ((100 : ℕ) : ℝ) (Set.Iic (1 / 101))
              = ENNReal.ofReal (1 - ((100 : ℝ) / 101) ^ 100))
    (harith : 2 * Real.exp (-(539 / 25 : ℝ))
                < ((86 : ℝ) / 101) ^ 100 * (1 - ((100 : ℝ) / 101) ^ 100)) :
    ¬ (∀ (α β r : ℝ), 0 < α → 0 < β → 1 ≤ r →
        ((betaMeasure α β).prod (betaMeasure α β))
          {p : ℝ × ℝ | r * (α / (α + β)) ≤ |p.1 - p.2|}
          ≤ ENNReal.ofReal (2 * Real.exp (-(1 / 8) * α * r ^ 2))) := by
  refine lemma5_range_ge_one_is_false hIci hIic (1 / 8) ?_
  have h : -(196 : ℝ) * (1 / 8) = -(49 / 2) := by norm_num
  rw [h]
  have h2 : -(49 / 2 : ℝ) < -(539 / 25) := by norm_num
  have h3 : Real.exp (-(49 / 2 : ℝ)) < Real.exp (-(539 / 25)) := Real.exp_lt_exp.mpr h2
  linarith [harith, h3]

end TSDPP
