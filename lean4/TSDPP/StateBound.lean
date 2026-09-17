/-
Copyright: formal artifact for INFOCOM'26 `infocom26.pdf`.
Released under Apache 2.0 license as described in the file LICENSE.

# R12a — Lemma 6, the state tail bound

The paper's Lemma 6 says that for any `ε > 0`, with probability at least `1 − ε`,

  `X_i(t; θ) ≤ ⌈log ε / log(1−θ)⌉`.

Both halves of that sentence are formalized here:

* `TSDPP.tail_le_eps` — the arithmetic core: with `d = ⌈log ε / log(1−θ)⌉` we have
  `(1−θ)^d ≤ ε`.  This is where `d ≥ log ε / log(1−θ)` is converted into
  `d·log(1−θ) ≤ log ε` (possible because `log(1−θ) < 0`, so the inequality reverses) and
  then exponentiated.  No probability is involved.
* `TSDPP.chain_path_no_reset` (in `TSDPP/Model.lean`) — the probabilistic half: the
  trajectory on which the chain has AoI `≥ d` after `d` slots is the single path
  `0 → 1 → … → d`, whose probability is the product of `d` upper-branch transitions,
  and that product is `(1−θ)^d`.

Together: `Pr(X_i(t) ≥ d) = (1−θ)^d ≤ ε`, so the complementary event has probability
`≥ 1 − ε`.  See GAP-3 in `DESIGN.md` for the separate, *unresolved* step the paper then
takes — passing from this high-probability statement to the T-free deterministic constants
`C`, `D` used in Eq (38).
-/
import Mathlib
import TSDPP.Model

namespace TSDPP

/-- **Lemma 6, arithmetic core.**  For `0 < θ < 1` and `0 < ε`, taking
`d = ⌈log ε / log(1−θ)⌉` gives `(1−θ)^d ≤ ε`.

The paper states this for `ε ∈ (0,1)`; no upper bound on `ε` is needed, and the proof below
never uses one, so the hypothesis is dropped.  (For `ε ≥ 1` the bound is trivial anyway.)

The ratio `log ε / log(1−θ)` is positive, so `Nat.le_ceil` bounds it by `d` from below;
since `log(1−θ) < 0`, multiplying by it *reverses* the inequality and yields
`d·log(1−θ) ≤ log ε`.  Exponentiating (which is monotone) and using `exp (log ε) = ε`
closes the goal. -/
theorem tail_le_eps {θ ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hε0 : 0 < ε) :
    (1 - θ) ^ ⌈Real.log ε / Real.log (1 - θ)⌉₊ ≤ ε := by
  have h1θ : 0 < 1 - θ := by linarith
  have hlogθ : Real.log (1 - θ) < 0 := Real.log_neg h1θ (by linarith)
  have hkey : ((⌈Real.log ε / Real.log (1 - θ)⌉₊ : ℕ) : ℝ) * Real.log (1 - θ) ≤ Real.log ε := by
    have hle : Real.log ε / Real.log (1 - θ)
        ≤ ((⌈Real.log ε / Real.log (1 - θ)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have := mul_le_mul_of_nonpos_right hle hlogθ.le
    rwa [div_mul_cancel₀ _ (ne_of_lt hlogθ)] at this
  calc (1 - θ) ^ ⌈Real.log ε / Real.log (1 - θ)⌉₊
      = Real.exp (((⌈Real.log ε / Real.log (1 - θ)⌉₊ : ℕ) : ℝ) * Real.log (1 - θ)) := by
        rw [← Real.exp_log (pow_pos h1θ _), Real.log_pow]
    _ ≤ Real.exp (Real.log ε) := Real.exp_le_exp.mpr hkey
    _ = ε := Real.exp_log hε0

end TSDPP
