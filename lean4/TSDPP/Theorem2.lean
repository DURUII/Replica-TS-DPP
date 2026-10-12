/-
Copyright (c) 2026 TSDPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# ROOT — Theorem 2, `BR(T) = O(√(L³ T log T))`, assembled

This module is the *headline*: it composes the four independently-closed pieces into one
statement about the Bayesian regret.

    Eq (38)  `Regret.regret_le`                 decompose over episodes and rounds
    Eq (39)  `Assembly.sum_inv_sqrt_weighted`   collapse `Σ_l C/√(η_l)` to `(C/√η)·2√m`
    Eq (40)  `Tail.tail_sum_le`                 the geometric tail beyond the truncation index
    final    `Rate.rate_core`                   pure arithmetic: `2L√(K₀Z) + B ≤ 8√(L⁴Z)`

The radius constant is `K₀ = 100/11`, not the paper's `8`: the artifact's Lemma 5 holds at
`c₀ = 11/100` (GAP-2b), and `K₀ = 1/c₀` is what keeps the paper's `2m/T` failure bound (see
`cards/R13.md`).  Consequently every `√(8·logT/η)` below is `√((100/11)·logT/η)` and the final
constant is `8 = 7 + 1` rather than the paper's `6 + 1` — the `+1` is the tail's, and
`2√(100/11) + 1 = 7.030227 > 7` (trap P-19).

The result is **not** stated in `O(·)` notation.  Mathlib's `Asymptotics` would need a filter on
`T` that the paper never pins down, and the paper's own `O(√(L³T log T))` is ambiguous between
`L` symbolic and `L` constant (GAP-4).  It is stated as the *concrete* bound with an explicit
constant, which is strictly stronger: `FIDELITY.md` §4 derives the `O(·)` claim from it by hand.

## What is assumed, and where it comes from

Every input below is a **hypothesis**, never an axiom.  Each is a paper result this module does
not re-derive, and each is stated so a reader can see exactly what is taken on faith:

* `hdecomp` — the paper's Eq (38) decomposition, **reproved here rather than quoted**.
  `Decomp.regret_decomp_episodeOf` supplies Lemma 3's combinatorial half, so the premise is
  *derived* in `theorem3_rate`, which calls `theorem2_rate` at `BR := ∑ s ∈ range (m*L), r s` and
  closes it at that instantiation.  It stays a premise of `theorem2_rate` itself, which is the
  general statement over an abstract `BR : ℝ`.  Lemma 3's *other* half — linearity of `∫` over a
  finite index set — is **not** removed: `Decomp.lean` says so in its own words, and says what
  remains is the assumption that there is something to decompose.
* `hper` — the per-round composition whose mathematical content is Lemma 4 of [28].  That lemma
  **is** proved, in its most general form: `Simulation.simulation_lemma` telescopes
  `∫ ω, ΔJ 0 ω ∂μ = ∑ t ∈ range L, ∫ ω, g t ω ∂μ` over an arbitrary measure space, with
  `bellman_step_le` supplying its Bellman recursion.  What is missing is the *instantiation*, not
  the lemma: this module does not import `Simulation`, and the trajectory law `P_{θ*}` together
  with the posterior samplings `θ^l ∼ Q^l` are formalized nowhere (`DESIGN.md` **GAP-7**).  So
  `hper` is a premise of **both** `theorem2_rate` and `theorem3_rate`, and it is the largest open
  input in this file.  `Simulation.lean`'s own card claims to discharge "*part of* `hper`", not all
  of it, and that is the accurate claim.
  (`R4` — the constrained policy of Eq (10),(12),(13) — is a *different* absent cluster, tabulated
  under "Out of scope" in `cards/README.md`; nothing in the DAG consumes it.  It is not the
  blocker.  Do not merge the two.)
* `Regret.regret_le` proves everything downstream of these two hypotheses.
* `hdelta` / `hηl` — Corollary 1's `α^l_i ≥ η·l` and the concentration radius `r^l_i`.  Rests on
  Lemma 5 of [45] (GAP-2) and Lemma 6 (GAP-3, where `C`, `D`, `η` are assumed `T`-free).
* `hB0` / `hBle` — the tail `B` beyond the truncation index is nonnegative and `O(√log T)`.
  **This is GAP-6**: the paper's printed constant in Eq (40) is not reconstructible, and
  `Tail.lean` proves the honest geometric bound instead.  `B` is an explicit parameter here so
  the gap cannot hide inside a constant.
  Where they are load-bearing, and where they are **inert**: `B` does not occur in the conclusion
  of `theorem2_rate` or of `theorem3_rate`, so in those two `hB0` and `hBle` are inert hypotheses
  — they are carried because the signature is uniform, not because the bound needs them.  They do
  real work only where `B` is being *absorbed*: the proof of `theorem2_concrete`, through
  `Rate.rate_core`'s `hBle`.  A reader who takes their presence in `theorem2_rate` as evidence
  that the tail has been dealt with there is reading them as something they are not.

## The tail is *not* dropped silently

`theorem2_withTail` keeps `B` visible on the right-hand side — that is the honest composite of
Eq (38)–(40).  `theorem2_concrete` then absorbs it using `hB0` and `hBle`, which is exactly the
step GAP-6 says the paper performs without justification.
-/
import Mathlib
import TSDPP.Decomp
import TSDPP.Regret
import TSDPP.Assembly
import TSDPP.Tail
import TSDPP.Rate

namespace TSDPP

open Finset

/-- **Eq (39), the collapse over episodes.**  `Σ_{l<m} Σ_{t<L} delta l t ≤ L·2√(K₀m log T/η)`
with `K₀ = 100/11` — the artifact's radius constant in place of the paper's `8`.

`sum_inv_sqrt_weighted` with `C = √(K₀ log T)` supplies `Σ_l √(K₀ log T/η_l) ≤ (√(K₀ log T)/√η)·2√m`;
the inner sum over the `L` rounds contributes the factor `L` because the concentration term does
not depend on which round it is.

The substitution also *weakens* the hypothesis `hdelta`: `√(K₀ logT/η)` is larger than
`√(8 logT/η)` by `√(100/88) = 1.066`, so anything that discharged the paper's radius discharges
this one a fortiori.  That is the direction the artifact needs — the concentration Lemma 5 it can
actually prove has the larger radius. -/
theorem eq39_collapse {m L : ℕ} {η logT : ℝ} (hη : 0 < η) (hlogT : 0 ≤ logT)
    (ηl : ℕ → ℝ) (hηl : ∀ l : ℕ, η * ((l : ℝ) + 1) ≤ ηl l)
    (delta : ℕ → ℕ → ℝ) (hdelta : ∀ l t, delta l t ≤ Real.sqrt ((100 / 11) * logT / ηl l)) :
    ∑ l ∈ range m, ∑ t ∈ range L, delta l t
      ≤ (L : ℝ) * (2 * Real.sqrt ((100 / 11) * (m : ℝ) * logT / η)) := by
  show ∑ l ∈ range m, ∑ t ∈ range L, delta l t
      ≤ (L : ℝ) * (2 * Real.sqrt ((100 / 11) * (m : ℝ) * logT / η))
  have hC8 : (0 : ℝ) ≤ (100 / 11) * logT := by positivity
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  -- Inner sum: `L` copies of the same per-episode term.
  have hinner : ∀ l ∈ range m, ∑ t ∈ range L, delta l t
      ≤ (L : ℝ) * Real.sqrt ((100 / 11) * logT / ηl l) := by
    intro l _
    have hstep : ∀ t ∈ range L, delta l t ≤ Real.sqrt ((100 / 11) * logT / ηl l) :=
      fun t _ => hdelta l t
    calc ∑ t ∈ range L, delta l t ≤ ∑ t ∈ range L, Real.sqrt ((100 / 11) * logT / ηl l) :=
          sum_le_sum hstep
      _ = (L : ℝ) * Real.sqrt ((100 / 11) * logT / ηl l) := by
          rw [sum_const, card_range, nsmul_eq_mul]
  -- `√(K₀ log T/η_l) = √(K₀ log T)/√(η_l)`, the shape `sum_inv_sqrt_weighted` consumes.
  have hsplit : ∀ l : ℕ, Real.sqrt ((100 / 11) * logT / ηl l)
      = Real.sqrt ((100 / 11) * logT) / Real.sqrt (ηl l) := fun l => Real.sqrt_div hC8 (ηl l)
  have hw := sum_inv_sqrt_weighted m (Real.sqrt_nonneg ((100 / 11) * logT)) hη ηl hηl
  calc ∑ l ∈ range m, ∑ t ∈ range L, delta l t
      ≤ ∑ l ∈ range m, (L : ℝ) * Real.sqrt ((100 / 11) * logT / ηl l) := sum_le_sum hinner
    _ = (L : ℝ) * ∑ l ∈ range m, Real.sqrt ((100 / 11) * logT / ηl l) := by rw [mul_sum]
    _ = (L : ℝ) * ∑ l ∈ range m, Real.sqrt ((100 / 11) * logT) / Real.sqrt (ηl l) := by
          simp_rw [hsplit]
    _ ≤ (L : ℝ) * ((Real.sqrt ((100 / 11) * logT) / Real.sqrt η) * (2 * Real.sqrt m)) :=
          mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg L)
    _ = (L : ℝ) * (2 * Real.sqrt ((100 / 11) * (m : ℝ) * logT / η)) := by
          congr 1
          rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ (100 / 11) * (m : ℝ) * logT)]
          have hs : Real.sqrt ((100 / 11) * (m : ℝ) * logT)
              = Real.sqrt ((100 / 11) * logT) * Real.sqrt (m : ℝ) := by
            rw [show (100 / 11) * (m : ℝ) * logT = ((100 / 11) * logT) * (m : ℝ) by ring,
              Real.sqrt_mul hC8]
          rw [hs]
          ring

/-- **Eq (38) + (39) + (40), with the tail kept visible.**  The honest composite: the regret is
bounded by the per-round coefficient `K` times the collapsed divergence *plus* the tail `B`. -/
theorem theorem2_withTail {m L : ℕ} {η logT K B : ℝ} (hη : 0 < η) (hlogT : 1 ≤ logT)
    (hK : 0 ≤ K) (hB0 : 0 ≤ B)
    (ηl : ℕ → ℝ) (hηl : ∀ l : ℕ, η * ((l : ℝ) + 1) ≤ ηl l)
    (BR : ℝ) (episodeRegret : ℕ → ℝ) (delta : ℕ → ℕ → ℝ)
    (hdecomp : BR = ∑ l ∈ range m, episodeRegret l)
    (hper : ∀ l, |episodeRegret l| ≤ K * ∑ t ∈ range L, delta l t)
    (hdelta : ∀ l t, delta l t ≤ Real.sqrt ((100 / 11) * logT / ηl l)) :
    |BR| ≤ K * ((L : ℝ) * (2 * Real.sqrt ((100 / 11) * (m : ℝ) * logT / η)) + B) := by
  show |BR| ≤ K * ((L : ℝ) * (2 * Real.sqrt ((100 / 11) * (m : ℝ) * logT / η)) + B)
  rw [hdecomp]
  have h38 : |∑ l ∈ range m, episodeRegret l|
      ≤ K * ∑ l ∈ range m, ∑ t ∈ range L, delta l t := regret_le episodeRegret delta hper
  have h39 : ∑ l ∈ range m, ∑ t ∈ range L, delta l t
      ≤ (L : ℝ) * (2 * Real.sqrt ((100 / 11) * (m : ℝ) * logT / η)) :=
    eq39_collapse hη (by linarith) ηl hηl delta hdelta
  have hmain : K * ∑ l ∈ range m, ∑ t ∈ range L, delta l t
      ≤ K * ((L : ℝ) * (2 * Real.sqrt ((100 / 11) * (m : ℝ) * logT / η))) :=
    mul_le_mul_of_nonneg_left h39 hK
  have hle : K * ((L : ℝ) * (2 * Real.sqrt ((100 / 11) * (m : ℝ) * logT / η)))
      ≤ K * ((L : ℝ) * (2 * Real.sqrt ((100 / 11) * (m : ℝ) * logT / η)) + B) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hB0) hK
  exact h38.trans (hmain.trans hle)

/-- **ROOT / Theorem 2, concrete form.**  With `T = m·L` and `K = ½C² + (2C²+2CD+C)·L`
(`Regret.regretCoeff`), the Bayesian regret satisfies

  `|BR| ≤ K · 8 · √(L³·T·log T / η)`.

Since `K = Θ(L)`, this is `Θ(L·√(L³T log T/η))`, one factor of `L` above the paper's
`O(√(L³T log T))`.  The extra `L` is `Rate.rate_core`'s doing: its `L ≤ L²` step and its
`B ≤ √(log T)` hypothesis both lift the tail onto the `L²` scale, which is what lets the paper's
radius constant survive at `K₀ = 100/11`.  The two agree as soon as `L` is bounded, the paper's
operative reading; `theorem2_rate` below keeps the `L` visible for exactly that reason, and
`Asymptotic.lean` records the growing-`L` reading.  The `8 = 7 + 1` comes from `Rate.rate_core`: `2L√(K₀Z) ≤ 7√(L⁴Z)` (the `L ≤ L²` slack
pays for `√(K₀)`, `K₀ = 100/11`) plus `B ≤ √(log T) ≤ √(L⁴Z)` (the hypothesis `η ≤ L⁴m`).  The
paper's own constant is `6 + 1` at its radius `√8`; at `K₀ = 100/11` the first summand is
`2√(100/11) = 6.030227`, so the same `+1` forces `8` (trap P-19: `2√(100/11) + 1 = 7.030227 > 7`).

The bound is stated for an *arbitrary* `BR : ℝ` satisfying the Eq (38) hypotheses, so it is
independent of how the regret was defined (Eq (18)) or estimated — that is the point of isolating
the arithmetic here. -/
theorem theorem2_concrete {m L : ℕ} {η logT K B : ℝ} (hη : 0 < η) (hlogT : 1 ≤ logT)
    (hL : 1 ≤ L) (hK : 0 ≤ K) (hB0 : 0 ≤ B) (hBle : B ≤ Real.sqrt logT)
    (hηT : η ≤ (L : ℝ) ^ 4 * (m : ℝ))
    (ηl : ℕ → ℝ) (hηl : ∀ l : ℕ, η * ((l : ℝ) + 1) ≤ ηl l)
    (BR : ℝ) (episodeRegret : ℕ → ℝ) (delta : ℕ → ℕ → ℝ)
    (hdecomp : BR = ∑ l ∈ range m, episodeRegret l)
    (hper : ∀ l, |episodeRegret l| ≤ K * ∑ t ∈ range L, delta l t)
    (hdelta : ∀ l t, delta l t ≤ Real.sqrt ((100 / 11) * logT / ηl l)) :
    |BR| ≤ K * (8 * Real.sqrt ((L : ℝ) ^ 3 * ((m : ℝ) * (L : ℝ)) * logT / η)) := by
  show |BR| ≤ K * (8 * Real.sqrt ((L : ℝ) ^ 3 * ((m : ℝ) * (L : ℝ)) * logT / η))
  have hwt := theorem2_withTail hη hlogT hK hB0 ηl hηl BR episodeRegret delta hdecomp hper hdelta
  -- `rate_core` bounds the bracket `2L√(K₀Z) + B` by `8√(L⁴Z)`; `K ≥ 0` carries it through.
  have h40 := rate_core (L := L) (m := m) (η := η) (logT := logT) (B := B) hη hlogT hL hBle hηT
  have hbracket : (L : ℝ) * (2 * Real.sqrt ((100 / 11) * (m : ℝ) * logT / η)) + B
      ≤ 8 * Real.sqrt ((L : ℝ) ^ 3 * ((m : ℝ) * (L : ℝ)) * logT / η) := by
    have hcomm : (L : ℝ) * (2 * Real.sqrt ((100 / 11) * (m : ℝ) * logT / η))
        = 2 * (L : ℝ) * Real.sqrt ((100 / 11) * (m : ℝ) * logT / η) := by ring
    rw [hcomm]
    exact h40
  exact hwt.trans (mul_le_mul_of_nonneg_left hbracket hK)

/-- **Theorem 2 with the `T`-free constant.**  Instantiating the abstract `K` of
`theorem2_concrete` with the paper's `regretCoeff C D L` and applying `regretCoeff_le_mul` yields
the rate with a coefficient that does not depend on the horizon:

  `|BR| ≤ c · L · √(L³·T·log T/η)`,  `c = 8·(½C² + 2C² + 2CD + C)`,  `T = m·L`.

This is as close to the paper's `BR(T) = O(√(L³T log T))` as can be stated without resolving
GAP-4: if `L` is bounded (the paper's operative assumption — it treats `L` as a constant), then
`c·L = Θ(1)` and this *is* `O(√(L³T log T))`.  If `L` grows with `T`, the paper's own abstract
rate `O(√(T log T))` is the other reading, and it is a different claim.  The `L` is therefore
kept visible rather than silently absorbed.

The docstring of `FIDELITY.md` §4 records this identification; this theorem is what makes that
section's remaining "hand arithmetic" a single line of algebra (`c` is literally a `let`). -/
theorem theorem2_rate {m L C D : ℕ} {η logT B : ℝ} (hη : 0 < η) (hlogT : 1 ≤ logT)
    (hL : 1 ≤ L) (hB0 : 0 ≤ B) (hBle : B ≤ Real.sqrt logT)
    (hηT : η ≤ (L : ℝ) ^ 4 * (m : ℝ))
    (ηl : ℕ → ℝ) (hηl : ∀ l : ℕ, η * ((l : ℝ) + 1) ≤ ηl l)
    (BR : ℝ) (episodeRegret : ℕ → ℝ) (delta : ℕ → ℕ → ℝ)
    (hdecomp : BR = ∑ l ∈ range m, episodeRegret l)
    (hper : ∀ l, |episodeRegret l| ≤ regretCoeff C D L * ∑ t ∈ range L, delta l t)
    (hdelta : ∀ l t, delta l t ≤ Real.sqrt ((100 / 11) * logT / ηl l)) :
    |BR| ≤ (8 * ((C : ℝ) ^ 2 / 2 + (2 * (C : ℝ) ^ 2 + 2 * (C : ℝ) * (D : ℝ) + (C : ℝ))))
             * ((L : ℝ) * Real.sqrt ((L : ℝ) ^ 3 * ((m : ℝ) * (L : ℝ)) * logT / η)) := by
  show |BR| ≤ (8 * ((C : ℝ) ^ 2 / 2 + (2 * (C : ℝ) ^ 2 + 2 * (C : ℝ) * (D : ℝ) + (C : ℝ))))
             * ((L : ℝ) * Real.sqrt ((L : ℝ) ^ 3 * ((m : ℝ) * (L : ℝ)) * logT / η))
  have hC0 : (0 : ℝ) ≤ (C : ℝ) := Nat.cast_nonneg C
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have hKc : 0 ≤ regretCoeff C D L := regretCoeff_nonneg C D L
  have hmain := theorem2_concrete
    hη hlogT hL hKc hB0 hBle hηT ηl hηl BR episodeRegret delta hdecomp hper hdelta
  have hle := regretCoeff_le_mul (C := C) (D := D) hL
  have hK'0 : 0 ≤ (C : ℝ) ^ 2 / 2 + (2 * (C : ℝ) ^ 2 + 2 * (C : ℝ) * (D : ℝ) + (C : ℝ)) := by
    positivity
  calc |BR|
      ≤ regretCoeff C D L * (8 * Real.sqrt ((L : ℝ) ^ 3 * ((m : ℝ) * (L : ℝ)) * logT / η)) :=
        hmain
    _ ≤ (((C : ℝ) ^ 2 / 2 + (2 * (C : ℝ) ^ 2 + 2 * (C : ℝ) * (D : ℝ) + (C : ℝ))) * (L : ℝ))
          * (8 * Real.sqrt ((L : ℝ) ^ 3 * ((m : ℝ) * (L : ℝ)) * logT / η)) :=
        mul_le_mul_of_nonneg_right hle (by positivity)
    _ = (8 * ((C : ℝ) ^ 2 / 2 + (2 * (C : ℝ) ^ 2 + 2 * (C : ℝ) * (D : ℝ) + (C : ℝ))))
          * ((L : ℝ) * Real.sqrt ((L : ℝ) ^ 3 * ((m : ℝ) * (L : ℝ)) * logT / η)) := by ring

/-- **Theorem 2 with `hdecomp` discharged (Lemma 3 applied).**

`theorem2_rate` assumed its regret decomposition as an opaque premise `hdecomp`.  Here the
cumulative regret is *literally* the round sum `∑ s ∈ range (m·L), r s`, so the episode
decomposition is supplied by `Decomp.regret_decomp` and `hdecomp` is gone: the only remaining
hypotheses are the per-episode bound `hper`, the concentration radius `hdelta`, and the standing
side conditions.

The episode regret is `Decomp.episodeOf r L l = ∑ t ∈ range L, r (l·L + t)` — episode `l` runs
over the `L` rounds starting at `l·L`. -/
theorem theorem3_rate {m L C D : ℕ} {η logT B : ℝ} (hη : 0 < η) (hlogT : 1 ≤ logT)
    (hL : 1 ≤ L) (hB0 : 0 ≤ B) (hBle : B ≤ Real.sqrt logT)
    (hηT : η ≤ (L : ℝ) ^ 4 * (m : ℝ))
    (ηl : ℕ → ℝ) (hηl : ∀ l : ℕ, η * ((l : ℝ) + 1) ≤ ηl l)
    (r : ℕ → ℝ) (delta : ℕ → ℕ → ℝ)
    (hper : ∀ l, |episodeOf r L l| ≤ regretCoeff C D L * ∑ t ∈ range L, delta l t)
    (hdelta : ∀ l t, delta l t ≤ Real.sqrt ((100 / 11) * logT / ηl l)) :
    |∑ s ∈ range (m * L), r s|
      ≤ (8 * ((C : ℝ) ^ 2 / 2 + (2 * (C : ℝ) ^ 2 + 2 * (C : ℝ) * (D : ℝ) + (C : ℝ))))
        * ((L : ℝ) * Real.sqrt ((L : ℝ) ^ 3 * ((m : ℝ) * (L : ℝ)) * logT / η)) := by
  show |∑ s ∈ range (m * L), r s|
      ≤ (8 * ((C : ℝ) ^ 2 / 2 + (2 * (C : ℝ) ^ 2 + 2 * (C : ℝ) * (D : ℝ) + (C : ℝ))))
        * ((L : ℝ) * Real.sqrt ((L : ℝ) ^ 3 * ((m : ℝ) * (L : ℝ)) * logT / η))
  -- Lemma 3: the horizon sums split into episodes, so `hdecomp` is derived, not assumed.
  have hdecomp : (∑ s ∈ range (m * L), r s) = ∑ l ∈ range m, episodeOf r L l :=
    regret_decomp_episodeOf r m L
  exact theorem2_rate hη hlogT hL hB0 hBle hηT ηl hηl
    (∑ s ∈ range (m * L), r s) (episodeOf r L) delta hdecomp hper hdelta

end TSDPP
