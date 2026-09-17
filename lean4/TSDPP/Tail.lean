/-
Copyright: formal artifact for INFOCOM'26 `infocom26.pdf`.
Released under Apache 2.0 license as described in the file LICENSE.

# The exponential tail of paper Eq (40), first half

(A sub-piece of card R14, "Eq (38)–(42) finite-sum assembly", in `DESIGN.md`.)

The paper's Theorem 2 controls the regret of the episode schedule.  After Eq (38) the
second term is a sum of concentration-failure probabilities,

  `Σ_{l=1}^{m} Σ_{t=1}^{L} 2·exp(−α^l_{A_t}·(r^l_{A_t})²/8)`.

On the episodes where `r^l_i = 1` — the early episodes `l ≤ ⌈8 log T/η⌉` — Corollary 1 of the
paper (`α^l_i ≥ η·l`) makes every summand at most `2·exp(−η·l/8)`.  Summing the `L` rounds of
an episode multiplies by `L`, and what is left is a *geometric series* in `exp(−η/8)`, whose
ratio is strictly below `1`.  That is the whole content of Eq (40):

  `Σ_{l=1}^{m} Σ_{t=1}^{L} 2·exp(−α^l_{A_t}/8) ≤ L · 2·exp(−η/8) / (1 − exp(−η/8))`.

**The exponent constant is a parameter, not a literal.**  The two declarations below are stated
for an arbitrary `c > 0`, with `c·η` in place of the paper's `η/8`: the paper's Eq (40) is the
instance `c = 1/8`, and the Theorem-2 chain consumes the instance `c = 11/100`.  That is forced
by Lemma 5, which this artifact can only prove with `c₀ = 11/100 < 1/8` (GAP-2b); the paper's own
value stays expressible because the statement is general, so the divergence is a *substitution*
at the use site and not a re-statement.  The condition the proof needs is `0 < c·η`, supplied
from `0 < c` and `0 < η`; nothing in the geometric argument depends on which `c` that is.

Both halves are formalized here and they are *pure arithmetic* — no bandit, no probability
measure and no filtration enters either statement.

* `TSDPP.geom_exp_sum_le` — the geometric series itself.  Writing `r = exp(−c·η)`, the
  identity `exp(−c·η(l+1)) = r^(l+1)` turns the summand into a power of a fixed ratio, and
  the finite partial sum `Σ_{l<N} r^l` is bounded by `1/(1−r)` with no appeal to the
  infinite-series API: the closed form `(Σ_{l<N} r^l)·(1−r) = 1 − r^N` and `r^N ≥ 0` give
  `(Σ_{l<N} r^l)·(1−r) ≤ 1`, and `1−r > 0` lets that be divided through.
* `TSDPP.tail_sum_le` — Eq (40) with the `L` rounds put back in.  The inner sum over the `L`
  rounds is a constant sum, hence `L` times one round, and `(L:ℝ) ≥ 0` pulls the factor out
  of the outer sum.

The one-line proof route `Real.exp_nat_mul` + `geom_sum_mul_neg` is taken deliberately over
`tsum_geometric_of_norm_lt_one`: the partial-sum bound is what Eq (40) actually needs, and it
keeps the whole file free of summability side conditions.

**What is deliberately not here.**  Three steps of Eq (40) are *not* formalized, and this
file makes no claim to them:

* the derivation `2·exp(−α^l_{A_t} (r^l_{A_t})²/8) ≤ 2·exp(−η·l/8)`, which consumes
  Corollary 1 (`α^l_i ≥ η·l`) together with `r^l_i ≤ 1`.  Corollary 1 is card R12b and is
  recorded as **GAP-3** in `DESIGN.md`; this card is the arithmetic that sits *after* it.
* the truncation to the early episodes `l ≤ ⌈8 log T/η⌉` on which `r^l_i = 1` holds.  The
  truncation only *shrinks* the sum, so it is invisible in the bound — which is exactly why
  the geometric bound above is stated for an arbitrary `N` rather than for the paper's `n`.
* the `2m/T` slack term that Eq (40) adds on the truncated tail.  It is additive, not part
  of the geometric factor.

Eq (40) is printed as a three-line chain (verified at 600 dpi, not from `paper.txt`).  The middle
inequality `≤ Σ_{l=1}^{n} L·2e^{−ηl/8}`, followed by the geometric sum, is what is formalized
here.  The `n` is **not** an OCR artefact — an earlier revision of this file wrongly said so: it
is the truncation index `n = ⌈8 log T/η⌉` introduced in the sentence above the display, and the
split `m = n + (m − n)` is what the additive `2m/T` accounts for.

The paper's **final** step, `≤ 1 − (16/η)e^{−η/8}·(1/T) + 2m/T`, is deliberately *not*
formalized, because it is false: its left-hand side is a `T`-independent constant
`L·2e^{−η/8}/(1−e^{−η/8})` while its right-hand side tends to `1`.  At the paper's own setting
`L = 20`, `η = 2` that reads `140.83 ≤ 1`.  See `DESIGN.md` GAP-6.  The true bound is the
geometric one proved here, which is `≤ 16L/η` via `1 − e^{−x} ≥ x·e^{−x}`.  Like the `2m/T` slack
it is `O(1)` in `T`, hence absorbed by the `O(L)` coefficient of Eq (38) into the same
`O(√(L³T log T))` rate — the theorem's conclusion survives, the intermediate step does not.
-/
import Mathlib

namespace TSDPP

open Finset

/-- The geometric decay of the concentration-failure terms of Eq (40), with the exponent
constant left as a parameter `c > 0`.  Indexing episodes by `l ↦ l + 1` so that the first
episode is `l = 0` (the paper's `l = 1`), the sum `Σ_l exp(−c·η(l+1))` is bounded by the full
geometric series `r / (1 − r)` with `r = exp(−c·η)`.

The parameter is not a convenience: the paper's `1/8` and the artifact's `11/100` (GAP-2b/2d)
are *both* wanted, and hard-coding either would make the other inexpressible.  The paper's value
is the instance `c = 1/8` (its `η(l+1)/8` is `(1/8)·η(l+1)`); the instance the Theorem-2 chain
consumes is `c = 11/100`, substituted at the use site.  The statement is genuinely about a
general `c`, so the divergence is a substitution rather than a re-statement. -/
theorem geom_exp_sum_le (η c : ℝ) (hη : 0 < η) (hc : 0 < c) (N : ℕ) :
    ∑ l ∈ range N, Real.exp (-(c * η * ((l : ℝ) + 1)))
      ≤ Real.exp (-(c * η)) / (1 - Real.exp (-(c * η))) := by
  show ∑ l ∈ range N, Real.exp (-(c * η * ((l : ℝ) + 1)))
      ≤ Real.exp (-(c * η)) / (1 - Real.exp (-(c * η)))
  have hcη : 0 < c * η := mul_pos hc hη
  have hpos : 0 < Real.exp (-(c * η)) := Real.exp_pos _
  have hlt1 : Real.exp (-(c * η)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hden : 0 < 1 - Real.exp (-(c * η)) := by linarith
  have hterm : ∀ l : ℕ,
      Real.exp (-(c * η * ((l : ℝ) + 1))) = Real.exp (-(c * η)) ^ (l + 1) := by
    intro l
    rw [← Real.exp_nat_mul (-(c * η)) (l + 1)]
    congr 1
    push_cast
    ring
  have hgeom : (∑ l ∈ range N, Real.exp (-(c * η)) ^ l) * (1 - Real.exp (-(c * η)))
      = 1 - Real.exp (-(c * η)) ^ N := geom_sum_mul_neg _ N
  have hbound : ∑ l ∈ range N, Real.exp (-(c * η)) ^ l
      ≤ 1 / (1 - Real.exp (-(c * η))) := by
    rw [le_div_iff₀ hden]
    rw [hgeom]
    have hpN : 0 ≤ Real.exp (-(c * η)) ^ N := pow_nonneg hpos.le N
    linarith
  calc ∑ l ∈ range N, Real.exp (-(c * η * ((l : ℝ) + 1)))
      = ∑ l ∈ range N, Real.exp (-(c * η)) ^ (l + 1) :=
        sum_congr rfl fun l _ => hterm l
    _ = (∑ l ∈ range N, Real.exp (-(c * η)) ^ l) * Real.exp (-(c * η)) := by
        rw [sum_mul]
        exact sum_congr rfl fun l _ => pow_succ _ _
    _ ≤ (1 / (1 - Real.exp (-(c * η)))) * Real.exp (-(c * η)) :=
        mul_le_mul_of_nonneg_right hbound hpos.le
    _ = Real.exp (-(c * η)) / (1 - Real.exp (-(c * η))) := by ring

/-- **Eq (40), first half.**  Summing over the `L` rounds of an episode multiplies by `L`,
and summing over episodes is `geom_exp_sum_le`.  The exponent constant `c` is the same
parameter, so the paper's `c = 1/8` and the artifact's `c = 11/100` are the same theorem. -/
theorem tail_sum_le (N L : ℕ) {η c : ℝ} (hη : 0 < η) (hc : 0 < c) :
    ∑ l ∈ range N, ∑ _t ∈ range L, 2 * Real.exp (-(c * η * ((l : ℝ) + 1)))
      ≤ (L : ℝ) * (2 * Real.exp (-(c * η)) / (1 - Real.exp (-(c * η)))) := by
  show ∑ l ∈ range N, ∑ _t ∈ range L, 2 * Real.exp (-(c * η * ((l : ℝ) + 1)))
      ≤ (L : ℝ) * (2 * Real.exp (-(c * η)) / (1 - Real.exp (-(c * η))))
  have hinner : ∀ l : ℕ, (∑ _t ∈ range L, 2 * Real.exp (-(c * η * ((l : ℝ) + 1))))
      = (L : ℝ) * (2 * Real.exp (-(c * η * ((l : ℝ) + 1)))) := by
    intro l
    rw [sum_const, card_range, nsmul_eq_mul]
  have htwo : ∑ l ∈ range N, 2 * Real.exp (-(c * η * ((l : ℝ) + 1)))
      = 2 * ∑ l ∈ range N, Real.exp (-(c * η * ((l : ℝ) + 1))) := by
    rw [mul_sum]
  calc ∑ l ∈ range N, ∑ _t ∈ range L, 2 * Real.exp (-(c * η * ((l : ℝ) + 1)))
      = ∑ l ∈ range N, (L : ℝ) * (2 * Real.exp (-(c * η * ((l : ℝ) + 1)))) :=
        sum_congr rfl fun l _ => hinner l
    _ = (L : ℝ) * ∑ l ∈ range N, 2 * Real.exp (-(c * η * ((l : ℝ) + 1))) := by
        rw [mul_sum]
    _ = (L : ℝ) * (2 * ∑ l ∈ range N, Real.exp (-(c * η * ((l : ℝ) + 1)))) := by
        rw [htwo]
    _ ≤ (L : ℝ) * (2 * (Real.exp (-(c * η)) / (1 - Real.exp (-(c * η))))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (geom_exp_sum_le η c hη hc N) (by norm_num))
          (Nat.cast_nonneg L)
    _ = (L : ℝ) * (2 * Real.exp (-(c * η)) / (1 - Real.exp (-(c * η)))) := by ring

end TSDPP
