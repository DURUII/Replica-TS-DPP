/-
Copyright (c) 2026 TSDPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# R16 — Theorem 2's final rate, `BR(T) = O(√(L³ T log T))`

The paper's Theorem 2 chains three inequalities.  Eq (38) bounds the regret by

  `BR(T) ≤ K · ( Σ_l L·√(K₀ log T/η_l) + [tail] )`,  `K = ½C² + (2C² + 2CD + C)·L`,

Eq (39) (formalized in `TSDPP/Assembly.lean`) collapses the sum to `2L√(K₀m log T/η)`, and
Eq (40) (formalized as `TSDPP.Tail.tail_sum_le`) bounds the tail by a constant `B ≥ 0`.
What is left is *pure arithmetic*: with `T = m·L`,

  `K·(2L√(K₀m log T/η) + B) ≤ K₀'·√(L³·T·log T/η)`.

**`K₀ = 100/11`, not the paper's `8`.**  The confidence-radius constant is the paper's `8` only
if Lemma 5 holds at the paper's `1/8`; this artifact proves it at `c₀ = 11/100` (GAP-2b), and the
radius constant must be `K₀ = 1/c₀` for the `2m/T` failure bound of Eq (33) to survive (see
`cards/R13.md`'s integration note).  The parameter is written `100/11` throughout the file rather
than folded into a `def`, so that the substitution stays visible and `grep -n '100 / 11'` finds
every site that depends on it.

Three facts do the work, none of them about bandits:

1. `mul_sqrt_eq_sqrt_sq_mul` — `a√x = √(a²x)` for `a ≥ 0`.  This is what turns the `L` in
   front of the sum into a radicand, giving the `L⁴ = L³·L` that the paper's rate exhibits
   as `L³·T = L³·mL`.
2. `two_mul_sqrt_ratio_le` — `2√((100/11)x) ≤ 7√x` for `x ≥ 0`, i.e. the `√(100/11)` of the
   confidence radius is paid for by the excess `L² ≥ 1` inside the radical.  This is the only
   place the constant is spent; it is why the explicit constant below is `8 = 7 + 1` rather
   than `7` (see `DESIGN.md` §6 trap P-19: the pair `L = m = η = log T = 1`, `B = 1` refutes
   any constant `< 2√(100/11) + 1 = 7.030227`, so `7` — which was valid at the paper's `2√8 + 1
   = 6.657` — no longer is).
3. `hηT : η ≤ L⁴m` — the tail's `O(1)` bound `B ≤ √(log T)` is swallowed by the main
   radical exactly when `log T ≤ L³·(mL)·log T/η`, i.e. `η ≤ L⁴m`.

The side condition `hηT` is **derived from** the paper's Corollary 1, not printed by it.  The
paper never states `η ≤ L⁴m`: what Corollary 1 gives is `η = ⌊L/(C+D)⌋` (the per-episode
selection count), hence `η ≤ L`, hence `η ≤ L ≤ L⁴m` for `L ≥ 1`, `m ≥ 1`.  So `hηT` follows from
Corollary 1 plus two trivial side conditions — it is derivable, not an independent hypothesis, and
it is not an artefact of the formalization either.  It is carried as a named premise only because
nothing else here needs the identification `η = ⌊L/(C+D)⌋`, and introducing it would pull in the
whole selection-counting argument for a factor that is spent at the very end.  (An earlier
revision of this docstring called `hηT` "the paper's own"; that overstated it.  `DESIGN.md` GAP-3
records Corollary 1's real status.)
-/
import Mathlib

namespace TSDPP

open Finset

/-- The paper's Eq (38) coefficient `K = ½C² + (2C² + 2CD + C)·L`.

This is exactly the value the paper prints: expanding `(½C² + LC) + 2C(C+D)L` (which is
Eq (36) plus Eq (37), the two per-round bounds) gives `½C² + 2C²L + 2CDL + CL`, i.e. the
printed form. -/
noncomputable def regretCoeff (C D L : ℕ) : ℝ :=
  (C : ℝ) ^ 2 / 2 + (2 * (C : ℝ) ^ 2 + 2 * (C : ℝ) * (D : ℝ) + (C : ℝ)) * (L : ℝ)

/-- The Eq (38) coefficient is nonnegative.  Every term is a product of `ℕ`-casts, so this holds
for *all* `C D L : ℕ` with no side condition.

This is stated as a named lemma rather than reproved at each use site because `theorem2_rate`
needs it as a hypothesis (`hKc`), and the same fact is quoted in `Regret.lean`'s documentation of
`episodeRegret_le` — a docstring reference to a declaration that did not exist until now. -/
theorem regretCoeff_nonneg (C D L : ℕ) : 0 ≤ regretCoeff C D L := by
  show 0 ≤ regretCoeff C D L
  unfold regretCoeff
  positivity

/-- `a·√x = √(a²·x)` for `a ≥ 0`: moving a nonnegative prefactor inside the radical.  The
`Real.sqrt_mul` step needs `0 ≤ a²`, and the `Real.sqrt_sq` step needs `0 ≤ a`. -/
lemma mul_sqrt_eq_sqrt_sq_mul {a x : ℝ} (ha : 0 ≤ a) :
    a * Real.sqrt x = Real.sqrt (a ^ 2 * x) := by
  show a * Real.sqrt x = Real.sqrt (a ^ 2 * x)
  rw [Real.sqrt_mul (pow_nonneg ha 2) x, Real.sqrt_sq ha]

/-- `2√((100/11)x) ≤ 7√x` for `x ≥ 0`.  Squaring both sides would need `4·(100/11)x ≤ 49x`, i.e.
`x ≥ 0` and `100/11 ≤ 49/4`; monotonicity of `√` on `(100/11)x ≤ (49/4)x` gives it directly,
with `√(49/4) = 7/2` supplied by `Real.sqrt_sq`.

Note the *bound* must be `49/4`, not `49`: `2√(Kx) ≤ 2·3√x` would need `9 ≥ 100/11`, which is
false — and `9 < 100/11` is precisely why the paper's `6` cannot be kept (trap P-19/P-48).  The
proof shape is unchanged from the paper's `2√(8x) ≤ 6√x`, only the numeral it is run at.

This is the artifact's replacement for the paper's `two_mul_sqrt_eight_le`: the radius constant
is `K₀ = 1/c₀ = 100/11` rather than the paper's `8` (see `cards/R13.md`).  Numerically
`2√(100/11) = 6.030227 ≤ 7` with `0.97` of slack, while `2√(100/11) ≤ 6` is false.  The `7` here
is this step's bound; the extra `+1` that makes the *final* constant `8` is the tail's, spent in
`rate_core`. -/
lemma two_mul_sqrt_ratio_le {x : ℝ} (hx : 0 ≤ x) :
    2 * Real.sqrt ((100 / 11) * x) ≤ 7 * Real.sqrt x := by
  show 2 * Real.sqrt ((100 / 11) * x) ≤ 7 * Real.sqrt x
  have hconst : (100 : ℝ) / 11 ≤ 49 / 4 := by norm_num
  have hle : Real.sqrt ((100 / 11) * x) ≤ Real.sqrt ((49 / 4) * x) :=
    Real.sqrt_le_sqrt (by nlinarith [mul_le_mul_of_nonneg_right hconst hx])
  have h49 : Real.sqrt ((49 / 4) * x) = (7 / 2) * Real.sqrt x := by
    rw [show (49 : ℝ) / 4 * x = ((7 : ℝ) / 2) ^ 2 * x by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ ((7 : ℝ) / 2) ^ 2),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (7 : ℝ) / 2)]
  linarith

/-- **Arithmetic core of Theorem 2's final rate.**  Everything the paper does between Eq (39)
and the final line, with the tail `B` kept as an opaque real: writing `Z = m·log T/η` for the
per-episode confidence term and `K₀ = 100/11` for the artifact's radius constant,

  `2L√(K₀Z) + B ≤ 8·√(L⁴·Z) = 8·√(L³·(mL)·log T/η)`.

The `8 = 7 + 1` splits as `2L√(K₀Z) ≤ 7√(L⁴Z)` (the `L ≤ L²` slack pays for `√(100/11)`, via
`two_mul_sqrt_ratio_le`) plus `B ≤ √(log T) ≤ √(L⁴Z)` (the hypothesis `η ≤ L⁴m`).  The paper's
own split is `6 + 1` with `K₀ = 8`; at `K₀ = 100/11` the first summand rises to `2√(100/11) =
6.030227`, so the same `+1` forces the constant up from `7` to `8`.  That is the only reason the
numeral differs from the paper's, and it is *forced*: `2√(100/11) + 1 = 7.030227 > 7` (trap P-19).

Trap P-14 (again): the hypotheses `0 ≤ B` and `1 ≤ m` were in the first draft, the linter
flagged both unused, and they were **dropped** rather than silenced — the statement is
strictly stronger without them.  `B < 0` is fine because the right-hand side is `≥ 0`; `m ≥ 1`
is never needed because the proof only ever uses `m ≥ 0`, via `Nat.cast_nonneg`. -/
lemma rate_core {L m : ℕ} {η logT B : ℝ}
    (hη : 0 < η) (hlogT : 1 ≤ logT) (hL : 1 ≤ L)
    (hBle : B ≤ Real.sqrt logT) (hηT : η ≤ (L : ℝ) ^ 4 * (m : ℝ)) :
    2 * (L : ℝ) * Real.sqrt ((100 / 11) * (m : ℝ) * logT / η) + B
      ≤ 8 * Real.sqrt ((L : ℝ) ^ 3 * ((m : ℝ) * (L : ℝ)) * logT / η) := by
  show 2 * (L : ℝ) * Real.sqrt ((100 / 11) * (m : ℝ) * logT / η) + B
      ≤ 8 * Real.sqrt ((L : ℝ) ^ 3 * ((m : ℝ) * (L : ℝ)) * logT / η)
  have hlogT0 : 0 ≤ logT := by linarith
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  set Z : ℝ := (m : ℝ) * logT / η with hZdef
  have hZ0 : 0 ≤ Z := by
    rw [hZdef]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg m) hlogT0) hη.le
  have hL4Z : 0 ≤ (L : ℝ) ^ 4 * Z :=
    mul_nonneg (pow_nonneg (Nat.cast_nonneg L) 4) hZ0
  have hstep1 :
      2 * (L : ℝ) * Real.sqrt ((100 / 11) * Z)
        ≤ 2 * ((L : ℝ) ^ 2 * Real.sqrt ((100 / 11) * Z)) := by
    show 2 * (L : ℝ) * Real.sqrt ((100 / 11) * Z)
        ≤ 2 * ((L : ℝ) ^ 2 * Real.sqrt ((100 / 11) * Z))
    have hs : 0 ≤ Real.sqrt ((100 / 11) * Z) := Real.sqrt_nonneg _
    have hL2 : (L : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith [hL1]
    nlinarith [mul_le_mul_of_nonneg_right hL2 hs]
  have hstep2 : 2 * ((L : ℝ) ^ 2 * Real.sqrt ((100 / 11) * Z))
      = 2 * Real.sqrt ((100 / 11) * ((L : ℝ) ^ 4 * Z)) := by
    show 2 * ((L : ℝ) ^ 2 * Real.sqrt ((100 / 11) * Z))
        = 2 * Real.sqrt ((100 / 11) * ((L : ℝ) ^ 4 * Z))
    rw [mul_sqrt_eq_sqrt_sq_mul (sq_nonneg (L : ℝ))]
    have hrad : ((L : ℝ) ^ 2) ^ 2 * ((100 / 11) * Z) = (100 / 11) * ((L : ℝ) ^ 4 * Z) := by ring
    rw [hrad]
  have hstep3 : 2 * Real.sqrt ((100 / 11) * ((L : ℝ) ^ 4 * Z))
      ≤ 7 * Real.sqrt ((L : ℝ) ^ 4 * Z) :=
    two_mul_sqrt_ratio_le hL4Z
  have hkey : 2 * (L : ℝ) * Real.sqrt ((100 / 11) * (m : ℝ) * logT / η)
      ≤ 7 * Real.sqrt ((L : ℝ) ^ 3 * ((m : ℝ) * (L : ℝ)) * logT / η) := by
    have h8 : (100 / 11) * (m : ℝ) * logT / η = (100 / 11) * Z := by rw [hZdef]; ring
    have hY : (L : ℝ) ^ 3 * ((m : ℝ) * (L : ℝ)) * logT / η = (L : ℝ) ^ 4 * Z := by
      rw [hZdef]; ring
    rw [h8, hY]
    calc 2 * (L : ℝ) * Real.sqrt ((100 / 11) * Z)
        ≤ 2 * ((L : ℝ) ^ 2 * Real.sqrt ((100 / 11) * Z)) := hstep1
      _ = 2 * Real.sqrt ((100 / 11) * ((L : ℝ) ^ 4 * Z)) := hstep2
      _ ≤ 7 * Real.sqrt ((L : ℝ) ^ 4 * Z) := hstep3
  have hBY : B ≤ Real.sqrt ((L : ℝ) ^ 3 * ((m : ℝ) * (L : ℝ)) * logT / η) := by
    have hY : (L : ℝ) ^ 3 * ((m : ℝ) * (L : ℝ)) * logT / η = (L : ℝ) ^ 4 * Z := by
      rw [hZdef]; ring
    rw [hY]
    refine hBle.trans (Real.sqrt_le_sqrt ?_)
    rw [hZdef, show (L : ℝ) ^ 4 * ((m : ℝ) * logT / η)
        = (L : ℝ) ^ 4 * ((m : ℝ) * logT) / η by ring]
    rw [le_div_iff₀ hη]
    nlinarith [mul_le_mul_of_nonneg_right hηT hlogT0]
  linarith

/-- `T`-free form of the Eq (38) coefficient: `regretCoeff C D L ≤ K'·L` with
`K' = ½C² + (2C²+2CD+C)` **independent of `L`**.  The only content is `C²/2 ≤ C²L/2`, i.e.
`L ≥ 1`; everything else is the common factor `(2C²+2CD+C)L`.

This is what turns the concrete bound `|BR| ≤ K·7√(L³T log T/η)` into the paper's asymptotic
rate: with `K ≤ K'L` and `L` bounded (GAP-4 — the paper never says whether `L` grows with `T`),
the coefficient is `Θ(1)` and the bound is `Θ(√(L³T log T))`. -/
theorem regretCoeff_le_mul {C D L : ℕ} (hL : 1 ≤ L) :
    regretCoeff C D L
      ≤ ((C : ℝ) ^ 2 / 2 + (2 * (C : ℝ) ^ 2 + 2 * (C : ℝ) * (D : ℝ) + (C : ℝ))) * (L : ℝ) := by
  show regretCoeff C D L
      ≤ ((C : ℝ) ^ 2 / 2 + (2 * (C : ℝ) ^ 2 + 2 * (C : ℝ) * (D : ℝ) + (C : ℝ))) * (L : ℝ)
  unfold regretCoeff
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hC2 : (0 : ℝ) ≤ (C : ℝ) ^ 2 := sq_nonneg _
  have hstep : (C : ℝ) ^ 2 / 2 ≤ (C : ℝ) ^ 2 * (L : ℝ) / 2 := by nlinarith
  nlinarith [mul_nonneg hC2 (by linarith : (0 : ℝ) ≤ (L : ℝ) - 1)]

end TSDPP
