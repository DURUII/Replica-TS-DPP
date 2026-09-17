/-
Copyright: formal artifact for INFOCOM'26 `infocom26.pdf`.
Released under Apache 2.0 license as described in the file LICENSE.

**The registered Lemma 5 target is FALSE, and this file proves it in Lean.**

The statement refuted here is the one this artifact registered (trap P-64 in `../DESIGN.md`):

    Pr(|X - Y| ≥ r·α/(α+β)) ≤ 2·exp(-c·α·r²),   X, Y iid `betaMeasure α β`,  **r ≥ 1**

with `c = 11/100` in the artifact and `c = 1/8` in the paper.  Both are refuted; the general-`c`
form below yields the sharp threshold `c* = 0.087918604136904736052`, so **no constant above
`0.08792` survives on `r ≥ 1`**.

## SCOPE — what this does *not* claim

Stated plainly, because the word "refutation" invites over-reading:

* This refutes the `r ≥ 1` statement.  It does **not** refute the paper's own Lemma 5, which
  `paper.pdf` p. 9 Eq (31) states **for all `0 ≤ r ≤ 1`**.  The witness sits at `r = 14`, entirely
  outside that range.  On `0 ≤ r ≤ 1` the paper's bound holds with room to spare: the worst ratio
  `Pr(|X-Y| ≥ rE(X)) / (2·exp(-αr²/8))` over a sweep of `(α, β, r)` is `0.393`, and as `r → 0⁺` the
  ratio tends to `1/2` from below, so that range cannot be violated at all.
* This does **not** refute the paper's theorem.  A proof step that does not go through does not make
  the theorem false — the theorem may well be true by another route.  What *is* established is that
  Eq (33) applies Lemma 5 at `r = max{1, √(8 log T/α)} ≥ 1`, outside the range the lemma is stated
  for.  Refuting the theorem itself would require a regret counterexample, and that needs the
  problem statement (Eq (10),(12),(13)) formalized — which this artifact never did (card `R4`).
* So the honest one-liner is: **the artifact's own registration was wrong, and the paper's *use* of
  Lemma 5 is invalid — not that the paper's theory is false.**  See `cards/L5-REFUTATION.md` §0.

## Why `α = 1` (this is the whole trick)

The refutation needs a **lower** bound on a probability, and every tool in `TSDPP/` (Markov,
Chernoff, union, Cantelli, Chebyshev) gives **upper** bounds.  The escape is elementary:

    {X ≥ t} × {Y ≤ u}  ⊆  {|X - Y| ≥ s}   whenever   s ≤ t - u,

so `Pr(|X-Y| ≥ s) ≥ Pr(X ≥ t)·Pr(Y ≤ u)`.  For `Beta(1, B)` both factors are closed-form
(`TSDPP/BetaOneCDF.lean`): `Pr(X ≥ t) = (1-t)^B` and `Pr(Y ≤ u) = 1 - (1-u)^B`.  Witness
`(α, β, r) = (1, 100, 14)`, `s = 14/101`, `t = 15/101`, `u = 1/101`, so `t - u = s` exactly.

The provable lower bound is `LB = (86/101)^100 · (1 - (100/101)^100)`, which exceeds the registered
right-hand side by **75.79×**; the true probability (`3.061996161029655566e-7`, verified
independently) exceeds it by **353.48×**.  The certificate is deliberately weak — it certifies
`75.79×` where the truth is `353.48×` — because a weak certificate that is *provable with Mathlib's
actual API* beats a sharp one that is not.

**Why not the numerically strongest witness?**  `(5, 500, 10)` needs a 500-term binomial;
`α ≥ 2` breaks the single-power density `B(1-x)^(B-1)` and drags in the incomplete Beta function,
which Mathlib does not have.  `α = 1` is what makes the analytic node a *polynomial* integral.
-/
import Mathlib
import TSDPP.BetaOneCDF

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TSDPP

/-! ## §1  The arithmetic residual

All of it reduces to `Real.add_one_le_exp` and `Real.log_le_sub_one_of_pos`; there is no `norm_num`
on a transcendental.  The slack is large (18.43× at the tightest link), so nothing here is delicate.
-/

/-- `(100/101)^100 ≤ 2/5`.  Via `log x ≤ x - 1` at `x = 101/100`, then `exp`; the finite Taylor sum
`∑_{i<4} (100/101)^i / i! = 2.642 ≥ 5/2` supplies the other half, so `n = 4` terms suffice. -/
theorem pow_100_101_le : ((100 : ℝ) / 101) ^ 100 ≤ 2 / 5 := by
  have hlog : Real.log (100 / 101 : ℝ) ≤ -(1 / 101 : ℝ) := by
    have hle := Real.log_le_sub_one_of_pos (x := (100 / 101 : ℝ)) (by norm_num)
    have hsub : (100 / 101 : ℝ) - 1 = -(1 / 101 : ℝ) := by norm_num
    simpa [hsub] using hle
  have hmul : (100 : ℝ) * Real.log (100 / 101 : ℝ) ≤ -(100 / 101 : ℝ) := by
    calc
      (100 : ℝ) * Real.log (100 / 101 : ℝ) ≤ (100 : ℝ) * -(1 / 101 : ℝ) :=
        mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 100)
      _ = -(100 / 101 : ℝ) := by norm_num
  have h1 : ((100 : ℝ) / 101) ^ 100 ≤ Real.exp (-(100 / 101 : ℝ)) := by
    rw [← Real.log_le_iff_le_exp (show (0 : ℝ) < ((100 : ℝ) / 101) ^ 100 from
      pow_pos (by norm_num) 100)]
    rw [Real.log_pow]
    exact hmul
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

/-- `exp(-750/43) ≤ (86/101)^100`.  Via `log x ≤ x - 1` at `x = 101/86`, so
`log (86/101) = -log (101/86) ≥ -15/86` and `100 · (-15/86) = -750/43`. -/
theorem exp_neg_le_pow_86_101 : Real.exp (-(750 / 43 : ℝ)) ≤ ((86 : ℝ) / 101) ^ 100 := by
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
  rw [← Real.le_log_iff_exp_le (show (0 : ℝ) < ((86 : ℝ) / 101) ^ 100 from
    pow_pos (by norm_num) 100)]
  rw [Real.log_pow]
  exact hmul

/-- The residual inequality, with the two exponentials separated:
`2·exp(-539/25) < (3/5)·exp(-750/43)`.  The key is `exp(4427/1075) > 10/3`, from
`Real.add_one_le_exp` — which gives only `5.118`, comfortably enough against the needed `3.333`. -/
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
    2 * Real.exp (-(539 / 25 : ℝ))
        = (2 * Real.exp (-(4427 / 1075 : ℝ))) * Real.exp (-(750 / 43 : ℝ)) := by
          rw [hsplit, Real.exp_add]; ring
    _ < (3 / 5 : ℝ) * Real.exp (-(750 / 43 : ℝ)) :=
      mul_lt_mul_of_pos_right hlt2 (Real.exp_pos (-(750 / 43 : ℝ)))

/-- The arithmetic residual the assembly consumes, stated against the certificate itself.
`2·exp(-539/25) = 8.662454487209e-10` versus `LB = 6.565190426654e-8`: slack **75.79×**. -/
theorem refute_arith :
    2 * Real.exp (-(539 / 25 : ℝ))
      < ((86 : ℝ) / 101) ^ 100 * (1 - ((100 : ℝ) / 101) ^ 100) := by
  have hle35 : (3 / 5 : ℝ) ≤ 1 - ((100 : ℝ) / 101) ^ 100 := by
    nlinarith [pow_100_101_le]
  have hpos_pow : (0 : ℝ) ≤ ((86 : ℝ) / 101) ^ 100 :=
    pow_nonneg (by norm_num : (0 : ℝ) ≤ 86 / 101) 100
  have hprod := mul_le_mul exp_neg_le_pow_86_101 hle35 (by norm_num : (0 : ℝ) ≤ 3 / 5) hpos_pow
  exact lt_of_lt_of_le arith_core (by simpa [mul_comm] using hprod)

/-! ## §2  The box containment

The one genuinely measure-theoretic step, and it is four lines of `linarith`.  Note the hypothesis
direction `s ≤ t - u`: writing it the other way round is trap P-69.
-/

/-- **Box containment.**  If `s ≤ t - u` and `0 ≤ s`, the rectangle `{X ≥ t} × {Y ≤ u}` is
contained in `{|X - Y| ≥ s}`.  The only point to check is `p₁ - p₂ ≥ t - u ≥ s ≥ 0`, so the
absolute value can be dropped. -/
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

/-! ## §3  The two `Beta(1,100)` tail values, instantiated

These were hypotheses of the assembly while `BetaOneCDF.lean` was in flight; they are now
consequences of `betaMeasure_one_Ici` / `betaMeasure_one_Iic` at `B = 100`, `t = 15/101`,
`u = 1/101`.  Both `t` and `u` lie in `[0,1]`, so both lemmas' side conditions hold.
-/

private lemma betaMeasure_one100_Ici :
    betaMeasure (1 : ℝ) ((100 : ℕ) : ℝ) (Set.Ici (15 / 101))
      = ENNReal.ofReal (((86 : ℝ) / 101) ^ 100) := by
  have h := betaMeasure_one_Ici 100 (by norm_num) (t := 15 / 101) (by norm_num) (by norm_num)
  have harg : (1 : ℝ) - 15 / 101 = 86 / 101 := by norm_num
  rwa [harg] at h

private lemma betaMeasure_one100_Iic :
    betaMeasure (1 : ℝ) ((100 : ℕ) : ℝ) (Set.Iic (1 / 101))
      = ENNReal.ofReal (1 - ((100 : ℝ) / 101) ^ 100) := by
  have h := betaMeasure_one_Iic 100 (by norm_num) (u := 1 / 101) (by norm_num) (by norm_num)
  have harg : (1 : ℝ) - 1 / 101 = 100 / 101 := by norm_num
  rwa [harg] at h

/-! ## §4  The refutation

Three theorems, in increasing specificity.  The general one is parametric in `c` and is where the
threshold comes from; the other two instantiate it at the artifact's constant and at the paper's
own.  The `1/8` instance is stated **separately** so that it does not depend on the artifact's
transposition: whatever one thinks of `11/100`, the constant printed on p. 9 also fails.
-/

/-- **The general form.**  For *any* constant `c` whose exponent at `r = 14` is beaten by the
certificate `LB = (86/101)^100 · (1 - (100/101)^100)`, the bound `2·exp(-c·α·r²)` is **false** on the
registered range `r ≥ 1`.  Since `LB = 6.5651904266542612343e-8`, the hypothesis holds for every
`c > 0.0879…`: **no constant above `0.087918604136904736052` survives on `r ≥ 1`.** -/
theorem lemma5_range_ge_one_is_false (c : ℝ)
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
  have : IsProbabilityMeasure (betaMeasure (1 : ℝ) ((100 : ℕ) : ℝ)) :=
    isProbabilityMeasureBeta (by norm_num) (by norm_num)
  have hprod : ((betaMeasure (1 : ℝ) ((100 : ℕ) : ℝ)).prod
        (betaMeasure (1 : ℝ) ((100 : ℕ) : ℝ)))
      (Set.Ici (15 / 101) ×ˢ Set.Iic (1 / 101))
      = ENNReal.ofReal (((86 : ℝ) / 101) ^ 100 * (1 - ((100 : ℝ) / 101) ^ 100)) := by
    rw [Measure.prod_prod, betaMeasure_one100_Ici, betaMeasure_one100_Iic,
      ← ENNReal.ofReal_mul (by positivity)]
  have hlt : ENNReal.ofReal (2 * Real.exp (-196 * c))
      < ((betaMeasure (1 : ℝ) ((100 : ℕ) : ℝ)).prod (betaMeasure (1 : ℝ) ((100 : ℕ) : ℝ)))
          {p : ℝ × ℝ | 14 / 101 ≤ |p.1 - p.2|} := by
    refine lt_of_lt_of_le ?_ hbox
    rw [hprod]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr harith
  exact (not_le_of_gt hlt) h0

/-- **The artifact's registered target is FALSE**: the constant `c₀ = 11/100` does not survive on
`r ≥ 1`.  This is trap P-64 made machine-checked. -/
theorem lemma5_as_registered_is_false :
    ¬ (∀ (α β r : ℝ), 0 < α → 0 < β → 1 ≤ r →
        ((betaMeasure α β).prod (betaMeasure α β))
          {p : ℝ × ℝ | r * (α / (α + β)) ≤ |p.1 - p.2|}
          ≤ ENNReal.ofReal (2 * Real.exp (-(11 / 100) * α * r ^ 2))) := by
  refine lemma5_range_ge_one_is_false (11 / 100) ?_
  have h : -(196 : ℝ) * (11 / 100) = -(539 / 25) := by norm_num
  rw [h]
  exact refute_arith

/-- **The paper's own constant `1/8` is FALSE on the range Eq (33) applies it to** (trap P-67, made
machine-checked).  This is the statement that does *not* go through the artifact's transposed
constant: whatever one thinks of `11/100`, the lemma with the `1/8` printed on p. 9 fails once it is
applied at `r = max{1, √(8 log T/α)} ≥ 1`, which is where Eq (33) uses it.

Derived from the same certificate, since `1/8 > 11/100` makes the required right-hand side smaller:
`exp(-49/2) < exp(-539/25)` because `49/2 = 24.5 > 21.56`. -/
theorem paper_lemma5_range_ge_one_is_false :
    ¬ (∀ (α β r : ℝ), 0 < α → 0 < β → 1 ≤ r →
        ((betaMeasure α β).prod (betaMeasure α β))
          {p : ℝ × ℝ | r * (α / (α + β)) ≤ |p.1 - p.2|}
          ≤ ENNReal.ofReal (2 * Real.exp (-(1 / 8) * α * r ^ 2))) := by
  refine lemma5_range_ge_one_is_false (1 / 8) ?_
  have h : -(196 : ℝ) * (1 / 8) = -(49 / 2) := by norm_num
  rw [h]
  have h2 : -(49 / 2 : ℝ) < -(539 / 25) := by norm_num
  have h3 : Real.exp (-(49 / 2 : ℝ)) < Real.exp (-(539 / 25)) := Real.exp_lt_exp.mpr h2
  linarith [refute_arith, h3]

end TSDPP
