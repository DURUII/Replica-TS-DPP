/-
Copyright: formal artifact for INFOCOM'26 `infocom26.pdf`.
Released under Apache 2.0 license as described in the file LICENSE.

# L3 — Lemma 3, the regret decomposition, no longer a hypothesis

`Theorem2.theorem2_rate` used to take

  `hdecomp : BR = ∑ l ∈ range m, episodeRegret l`

as an opaque premise.  That premise is the *combinatorial* half of the paper's Lemma 3, and it is
a theorem: the horizon `T = m·L` is cut into `m` blocks of `L` consecutive rounds, and a sum over
`range (m·L)` splits into a double sum over `range m` and `range L`.

This module proves it, so `hdecomp` can be *derived* rather than assumed — by `theorem3_rate`, which
lives in `Theorem2.lean` and instantiates `BR := ∑ s ∈ range (m*L), r s`.  (`theorem3_rate` is *not*
below in this file: this module imports only `Mathlib` and cannot see it.  The original wording said
"below", which sent a reader looking for a declaration that is not here.)

## What is and is not removed

The paper's Lemma 3 has two halves:

1. `BR(T) = E[∑_{t=1}^T r*(t)] − E[∑_{t=1}^T r(t)]` is split by **linearity of expectation** and
   by **episode**.  Eq (27)/(28) write the episode split in terms of value functions `J`; that
   rewriting is the definition of the per-episode regret, not new mathematics.
2. The resulting inner object is a sum over the `L` rounds of one episode.

Half 2 is `sum_range_blocks` below — pure combinatorics, closed here with no hypotheses at all.
Half 1 is linearity of `∫` over a finite index set (`MeasureTheory.integral_finset_sum`), which
requires the probability space and the round-regret process `r` to be *set up*; until they are,
`BR` enters `theorem3_rate` as an explicit function `r : ℕ → ℝ` rather than as an opaque real.
That is the honest residue: what disappears is the assumption that the decomposition *holds*, not
the assumption that there is something to decompose.
-/
import Mathlib

namespace TSDPP

open Finset

/-- **Block splitting of a `range` sum.**  A sum over `range (m·L)` is the sum over `m` blocks of
`L` consecutive indices, the `l`-th block starting at `l·L`.

Stated for an arbitrary additive commutative monoid so it applies to `ℝ` and to any future
codomain.  The proof is induction on `m`, using `Finset.sum_range_add` to peel off the last block:
`(k+1)·L = k·L + L`, so `range ((k+1)·L) = range (k·L)` followed by `range L` shifted by `k·L`. -/
theorem sum_range_blocks {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m L : ℕ) :
    ∑ s ∈ range (m * L), f s = ∑ l ∈ range m, ∑ t ∈ range L, f (l * L + t) := by
  show ∑ s ∈ range (m * L), f s = ∑ l ∈ range m, ∑ t ∈ range L, f (l * L + t)
  induction m with
  | zero => simp
  | succ k ih =>
      -- `(k+1)·L = k·L + L`, so the last block is `range L` shifted by `k·L`; that is exactly
      -- the `l = k` summand of the right-hand side.  No `Ring`/`Nat.add_comm` rewriting is
      -- needed: `sum_range_add` produces `f (k * L + x)`, already the paper's indexing.
      rw [Nat.succ_mul, sum_range_add f (k * L) L, ih, sum_range_succ]

/-- **L3, in the shape `Theorem2` consumes.**  With the horizon `T = m·L` and the per-episode
regret defined as the sum of the per-round regret over that episode's `L` rounds, the total
regret is the sum of the episode regrets.  This is the former `hdecomp` hypothesis, discharged. -/
theorem regret_decomp (r : ℕ → ℝ) (m L : ℕ) :
    (∑ s ∈ range (m * L), r s)
      = ∑ l ∈ range m, ∑ t ∈ range L, r (l * L + t) :=
  sum_range_blocks r m L

/-- The per-episode regret induced by a per-round regret process, matching the paper's episode
indexing: episode `l` runs over rounds `l·L, …, l·L + L − 1`. -/
def episodeOf (r : ℕ → ℝ) (L l : ℕ) : ℝ := ∑ t ∈ range L, r (l * L + t)

/-- Restatement of `regret_decomp` through `episodeOf`, which is how it is used downstream. -/
theorem regret_decomp_episodeOf (r : ℕ → ℝ) (m L : ℕ) :
    (∑ s ∈ range (m * L), r s) = ∑ l ∈ range m, episodeOf r L l := by
  show (∑ s ∈ range (m * L), r s) = ∑ l ∈ range m, episodeOf r L l
  rw [regret_decomp]
  rfl

end TSDPP
