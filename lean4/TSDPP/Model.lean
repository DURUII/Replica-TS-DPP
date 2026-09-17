/-
Copyright: formal artifact for INFOCOM'26 `infocom26.pdf`.
Released under Apache 2.0 license as described in the file LICENSE.

# R1, R2, R3, R8, R15 — the system model

The paper's model is three definitions and two identities:

* **R1** Eq (2)–(3): the AoI of an event is a Markov chain on `ℕ` that resets to `0` with
  probability `θ` and otherwise increments.  `TSDPP.chainPMF` is its transition kernel and
  `TSDPP.chainPMF_sum_one` says it is a probability mass function.
* **R2** Eq (4): the AoI of an event *copy* in the platform.  `TSDPP.copyStep` is the
  one-slot recursion; `TSDPP.copyStep_iterate` is the closed form the paper uses silently
  everywhere afterwards — `δ` slots after the arm was last pulled at state `λ`, the copy
  AoI is `λ + δ`, i.e. the "record" `(λ, δ)` of Lemma 2.
* **R3** Eq (9): the per-slot penalty `r(t) = Σ_i γ_i Y_i(t)` telescopes.  Because only one
  arm is pulled, `r(t)` differs from `Σ_i γ_i Y_i(t−1) + 1` by exactly
  `γ_{A_t}·(X_{A_t} − Y_{A_t})`.  This is the paper's Eq (9) — see GAP-5 in `DESIGN.md` for
  the index convention pinned here.
* **R8** Lemma 1: the belief-DPP policy is a *deterministic* policy mapping.
  `TSDPP.bestArm` is the tie-broken maximiser and `TSDPP.bestArm_spec` its specification.
* **R15** Eq (35): since Eq (9) is additive in the observed state `X_a` and everything else
  cancels, the difference of the expected penalties under `θ*` and `θ` is
  `γ_a·(E_{θ*}[X_a] − E_θ[X_a])` — the two belief means of `TSDPP/Belief.lean`.
-/
import Mathlib
import TSDPP.Belief

namespace TSDPP

open Finset

/-! ## R1 — the AoI Markov chain (Eq (2), Eq (3)) -/

/-- Paper Eq (2)–(3).  `chainPMF θ x y` is `Pr(X_i(t+1) = y | X_i(t) = x)`: the chain jumps
to `0` with probability `θ` (the event occurred) and to `x + 1` with probability `1 − θ`.
The two branches are disjoint because `x + 1 ≠ 0`. -/
noncomputable def chainPMF (θ : ℝ) (x y : ℕ) : ℝ :=
  if y = 0 then θ else if y = x + 1 then 1 - θ else 0

lemma chainPMF_zero (θ : ℝ) (x : ℕ) : chainPMF θ x 0 = θ := by
  simp [chainPMF]

lemma chainPMF_succ (θ : ℝ) (x : ℕ) : chainPMF θ x (x + 1) = 1 - θ := by
  simp only [chainPMF, Nat.succ_ne_zero, ↓reduceIte]

lemma chainPMF_of_other {θ : ℝ} {x y : ℕ} (h0 : y ≠ 0) (h1 : y ≠ x + 1) :
    chainPMF θ x y = 0 := by
  simp only [chainPMF, h0, ↓reduceIte, h1]

/-- R1: Eq (2)–(3) really is a probability mass function.  Its support is `{0, x+1}`, which
is contained in `range (x + 2)`. -/
theorem chainPMF_sum_one (θ : ℝ) (x : ℕ) : ∑ y ∈ range (x + 2), chainPMF θ x y = 1 := by
  have hsub : ∑ y ∈ range (x + 2), chainPMF θ x y
      = ∑ y ∈ ({0, x + 1} : Finset ℕ), chainPMF θ x y := by
    refine (sum_subset (s₁ := ({0, x + 1} : Finset ℕ)) (s₂ := range (x + 2))
      (f := chainPMF θ x) ?_ ?_).symm
    · intro y hy
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl <;> simp
    · intro y _ hy
      simp only [mem_insert, mem_singleton, not_or] at hy
      exact chainPMF_of_other hy.1 hy.2
  rw [hsub, sum_insert (by simp), sum_singleton, chainPMF_zero, chainPMF_succ]
  ring

/-- R1, the path used by Lemma 6.  The probability of the *specific* trajectory
`0 → 1 → … → d` — "the event never occurs during the first `d` slots" — is the product of
the `d` upper-branch transitions, and equals `(1−θ)^d`.  `TSDPP/StateBound.lean` turns this
into the paper's Lemma 6. -/
theorem chain_path_no_reset (θ : ℝ) (d : ℕ) :
    ∏ x ∈ range d, chainPMF θ x (x + 1) = (1 - θ) ^ d := by
  rw [prod_congr rfl fun x _ => chainPMF_succ θ x, prod_const, card_range]

/-! ## R2 — the AoI of an event copy (Eq (4)) -/

/-- Paper Eq (4): one slot of the copy-AoI recursion.  If the arm is pulled, the copy
refreshes to the event's current AoI plus one slot of transmission; otherwise it ages. -/
def copyStep (sel : Bool) (Xprev Yprev : ℕ) : ℕ := if sel then Xprev + 1 else Yprev + 1

lemma copyStep_self (Xprev Yprev : ℕ) : copyStep true Xprev Yprev = Xprev + 1 := rfl
lemma copyStep_other (Xprev Yprev : ℕ) : copyStep false Xprev Yprev = Yprev + 1 := rfl

/-- R2, iterated.  If the arm has not been pulled for `δ` slots since its state was `λ`,
the copy AoI is `λ + δ`.  This is the "record" `(λ_i, δ_i)` that Lemma 2 conditions on, and
it is what makes the belief law `TSDPP.pmf` a function of `(λ, δ)` alone. -/
theorem copyStep_iterate (lam δ : ℕ) :
    (fun y : ℕ => copyStep false lam y)^[δ] lam = lam + δ := by
  induction δ with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [copyStep_other]
    omega

/-! ## R3 — Eq (9), the per-slot penalty -/

/-- Paper Eq (9).  With `γ` the event weights (the paper assumes `Σ_i γ_i = 1`, `γ_i ≥ 0`),
`Y` the copy AoI *before* the slot and `X` the event AoI before the slot, the new penalty
`Σ_i γ_i Y_i(t)` equals the old penalty plus `1` plus the correction for the pulled arm.

Index convention (GAP-5): Eq (4) refreshes the copy from `X_i(t−1)`, so the identity is
exact with `X_i(t−1)`.  The paper prints `X_{A_t}(t)` in Eq (9), which agrees only if the
event AoI happens to be unchanged at that slot; the off-by-one does not affect Eq (35),
whose two sides both use the same convention. -/
theorem penalty_identity {N : ℕ} (γ : Fin N → ℝ) (hγ : ∑ i, γ i = 1)
    (a : Fin N) (X Y : Fin N → ℕ) :
    ∑ i, γ i * (if i = a then (X i : ℝ) + 1 else (Y i : ℝ) + 1)
      = (∑ i, γ i * (Y i : ℝ)) + 1 + γ a * ((X a : ℝ) - (Y a : ℝ)) := by
  have hterm : ∀ i, γ i * (if i = a then (X i : ℝ) + 1 else (Y i : ℝ) + 1)
      = γ i * ((Y i : ℝ) + 1) + (if i = a then γ i * ((X i : ℝ) - (Y a : ℝ)) else 0) := by
    intro i
    by_cases hia : i = a
    · subst hia; rw [ite_eq_left rfl]; simp only [ite_true]; ring
    · simp [hia]
  rw [sum_congr rfl fun i _ => hterm i, sum_add_distrib]
  have hsplit : ∑ i, γ i * ((Y i : ℝ) + 1) = (∑ i, γ i * (Y i : ℝ)) + 1 := by
    simp_rw [mul_add, mul_one]
    rw [sum_add_distrib, hγ]
  have hpick : ∑ i, (if i = a then γ i * ((X i : ℝ) - (Y a : ℝ)) else 0)
      = γ a * ((X a : ℝ) - (Y a : ℝ)) := by
    rw [sum_ite_eq' Finset.univ a fun i => γ i * ((X i : ℝ) - (Y a : ℝ)), ite_eq_left (mem_univ a)]
  rw [hsplit, hpick]

/-! ## R8 — Lemma 1: the belief-DPP policy is deterministic -/

/-- The tie-broken maximum used by the belief-DPP policy: the arm maximising the belief DPP
index.  Because it is a *function* of the index vector, and the index vector is a function
of the history, the induced policy mapping is deterministic — which is the content of the
paper's Lemma 1. -/
noncomputable def bestArm {N : ℕ} [Nonempty (Fin N)] (idx : Fin N → ℝ) : Fin N :=
  (Finset.univ.exists_max_image idx Finset.univ_nonempty).choose

/-- Specification of `bestArm`: it really is a maximiser of the index. -/
theorem bestArm_spec {N : ℕ} [Nonempty (Fin N)] (idx : Fin N → ℝ) :
    ∀ i, idx i ≤ idx (bestArm idx) := by
  intro i
  exact (Finset.univ.exists_max_image idx Finset.univ_nonempty).choose_spec.2 i (mem_univ i)

/-- R8 in the form the paper uses it.  Two histories that induce the same belief induce the
same action: the belief-DPP policy is a deterministic policy mapping, so the action `A_t` is
a *function* of `H_{t−1}` and is therefore literally the same object under `θ*` and under
`θ` — the fact Eq (34)–(37) rely on. -/
theorem bestArm_congr {N : ℕ} [Nonempty (Fin N)] {idx idx' : Fin N → ℝ} (h : idx = idx') :
    bestArm idx = bestArm idx' := by rw [h]

/-! ## R15 — Eq (35), the penalty difference -/

/-- The expected per-slot penalty given the pre-slot history, as a function of the belief
mean `m` of the arm that is about to be pulled; this is Eq (9) with `E[X_a] = m`. -/
noncomputable def expPenalty {N : ℕ} (γ : Fin N → ℝ) (a : Fin N) (Yprev : Fin N → ℕ)
    (m : ℝ) : ℝ :=
  (∑ i, γ i * (Yprev i : ℝ)) + 1 + γ a * (m - (Yprev a : ℝ))

/-- **Eq (35).**  Under `θ*` and under `θ` the *same* arm `a` is pulled on the *same*
history (`TSDPP.bestArm_congr`, i.e. Lemma 1), so the pre-slot penalty `Σ_i γ_i Y_i(t−1)`
and the `+1` cancel between the two expectations, leaving exactly the difference of the
belief means of arm `a`. -/
theorem penalty_diff {N : ℕ} (γ : Fin N → ℝ) (a : Fin N) (Yprev : Fin N → ℕ) (m m' : ℝ) :
    expPenalty γ a Yprev m - expPenalty γ a Yprev m' = γ a * (m - m') := by
  unfold expPenalty
  ring

end TSDPP
