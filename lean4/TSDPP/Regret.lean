/-
Copyright: formal artifact for INFOCOM'26 `infocom26.pdf`.
Released under Apache 2.0 license as described in the file LICENSE.

# R10, R11 — Eq (36), Eq (37), Eq (38)

This is the bridge from the *belief law* to the *regret*.  Three steps.

* **Eq (36)** (`perRoundPenaltyDiff_le`).  By Eq (35) the per-round penalty difference is
  `γ_{A_t}·(E_{θ*}[X] − E_{θ_l}[X])` — the difference of the belief *means*.  Lemma 2's
  Eq (24) bounds that difference by `(δ(δ−1)/2 + δ(λ+δ))|θ* − θ_l|`, and Lemma 6 supplies
  `δ ≤ C` while an AoI inside an episode of length `L` satisfies `λ + δ = Y_i(t−1) ≤ L`.
  This gives the paper's `(½C² + LC)`.

  **Derivation note.**  The paper writes `LC`, not `C(C+D)`.  Both are available from
  Lemma 6 (`λ + δ ≤ C + D`); `LC` is the one that matches Eq (38)'s printed constant, and
  it is valid because the copy-AoI is trivially bounded by the episode length `L`.  No
  hypothesis of the paper is lost — the two routes differ only in which of two true bounds
  is spent.

* **Eq (37)** (`stateTerm_le`).  The value-function term of the Bellman difference.  Lemma 2's
  Eq (23) bounds the ℓ¹ distance by `2δ|θ* − θ_l| ≤ 2C|θ* − θ_l|`, and the value function
  satisfies `|J| ≤ L·(C + D)` (at most `L` rounds remain, each of penalty at most `C + D`);
  this gives the paper's `2C(C+D)L`.

* **Eq (38)** (`episodeRegret_le`, `regret_le`).  Lemma 4 decomposes an episode's regret
  into a sum of Bellman differences over the `L` rounds, so the per-round bounds of Eq (36)
  and Eq (37) are applied round by round and the resulting `K·|θ*_{A_t} − θ_{A_t}|` terms
  are summed.  **Lemma 3 and Lemma 4 are results of [28] that the paper cites rather than
  proves**; the code below therefore takes the decomposition as a *hypothesis* and proves
  the assembly, rather than axiomatising it.

The paper's Eq (38) coefficient `½C² + (2C²+2CD+C)L` expands to `(½C² + LC) + 2C(C+D)L` —
exactly Eq (36) plus Eq (37).  `scripts/numeric_check.py` re-checks that expansion.
-/
import Mathlib
import TSDPP.Lipschitz

namespace TSDPP

open Set Finset

/-! ## Eq (36) — the per-round penalty difference -/

/-- Lemma 2's Eq (24) restated as a bound on the difference of belief *means*.

`∑_x x·P^x` is the belief state `X^b_i(t)` of Eq (16); the difference of the two means is
`∑_x x·(P^x − P'^x)`, and the triangle inequality plus Eq (24) bounds it. -/
theorem beliefMean_diff_le {θ θ' : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) (hθ' : θ' ∈ Icc (0 : ℝ) 1)
    (lam δ : ℕ) :
    |∑ x ∈ range (lam + δ + 1), (x : ℝ) * pmf θ lam δ x
      - ∑ x ∈ range (lam + δ + 1), (x : ℝ) * pmf θ' lam δ x|
      ≤ ((δ : ℝ) * ((δ : ℝ) - 1) / 2 + (δ : ℝ) * ((lam : ℝ) + (δ : ℝ))) * |θ - θ'| := by
  show |∑ x ∈ range (lam + δ + 1), (x : ℝ) * pmf θ lam δ x
      - ∑ x ∈ range (lam + δ + 1), (x : ℝ) * pmf θ' lam δ x| ≤ _
  rw [← sum_sub_distrib]
  calc |∑ x ∈ range (lam + δ + 1),
          ((x : ℝ) * pmf θ lam δ x - (x : ℝ) * pmf θ' lam δ x)|
      ≤ ∑ x ∈ range (lam + δ + 1),
          |(x : ℝ) * pmf θ lam δ x - (x : ℝ) * pmf θ' lam δ x| :=
        abs_sum_le_sum_abs _ _
    _ = ∑ x ∈ range (lam + δ + 1), (x : ℝ) * |pmf θ lam δ x - pmf θ' lam δ x| := by
        refine sum_congr rfl fun x _ => ?_
        rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg x)]
    _ ≤ ((δ : ℝ) * ((δ : ℝ) - 1) / 2 + (δ : ℝ) * ((lam : ℝ) + (δ : ℝ))) * |θ - θ'| :=
        firstMoment_lipschitz θ θ' hθ hθ' lam δ

/-! ## Eq (36) — the paper's `(½C² + LC)` -/

/-- A probability vector over arms is bounded by `1`; in particular `γ_{A_t} ≤ 1`. -/
lemma weight_le_one {N : ℕ} {γ : Fin N → ℝ} (hγ0 : ∀ i, 0 ≤ γ i) (hγ1 : ∑ i, γ i = 1)
    (a : Fin N) : γ a ≤ 1 := by
  show γ a ≤ 1
  have h := Finset.single_le_sum (s := Finset.univ) (f := γ) (fun i _ => hγ0 i) (mem_univ a)
  rwa [hγ1] at h

/-- The coefficient comparison behind Eq (36): with `δ ≤ C` and `λ + δ ≤ L`, the Lemma 2
constant `δ(δ−1)/2 + δ(λ+δ)` is at most `C²/2 + C·L`. -/
lemma meanCoeff_le {C L lam δ : ℕ} (hδ : δ ≤ C) (hY : lam + δ ≤ L) :
    (δ : ℝ) * ((δ : ℝ) - 1) / 2 + (δ : ℝ) * ((lam : ℝ) + (δ : ℝ))
      ≤ (C : ℝ) ^ 2 / 2 + (C : ℝ) * (L : ℝ) := by
  show _ ≤ (C : ℝ) ^ 2 / 2 + (C : ℝ) * (L : ℝ)
  have hδR : (δ : ℝ) ≤ (C : ℝ) := by exact_mod_cast hδ
  have hYR : (lam : ℝ) + (δ : ℝ) ≤ (L : ℝ) := by exact_mod_cast hY
  have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := Nat.cast_nonneg δ
  have hC0 : (0 : ℝ) ≤ (C : ℝ) := Nat.cast_nonneg C
  have hsq : (δ : ℝ) * ((δ : ℝ) - 1) / 2 ≤ (C : ℝ) ^ 2 / 2 := by
    have h1 : (δ : ℝ) * ((δ : ℝ) - 1) ≤ (δ : ℝ) ^ 2 := by nlinarith
    have h2 : (δ : ℝ) ^ 2 ≤ (C : ℝ) ^ 2 := by
      simpa using pow_le_pow_left₀ hδ0 hδR 2
    linarith
  have hmul : (δ : ℝ) * ((lam : ℝ) + (δ : ℝ)) ≤ (C : ℝ) * (L : ℝ) :=
    mul_le_mul hδR hYR (by positivity) hC0
  linarith

/-- **Eq (36).**  `γ` is the event-weight vector (`γ_i ≥ 0`, `Σ_i γ_i = 1`), `a = A_t` the
arm pulled at round `t`, `δ` the number of rounds since `a` was last pulled, `λ + δ` the
copy-AoI `Y_a(t−1)`.  Under Lemma 6's `δ ≤ C` and the trivial `Y_a(t−1) ≤ L`,

  `|E_{θ*} r(t | H_{t−1}) − E_{θ_l} r(t | H_{t−1})| ≤ (½C² + LC)·|θ*_a − θ_l_a|`.

The two expectations are Eq (35), i.e. `γ_a` times the difference of the belief means;
`weight_le_one` disposes of the `γ_a` factor. -/
theorem perRoundPenaltyDiff_le {N : ℕ} {γ : Fin N → ℝ} (hγ0 : ∀ i, 0 ≤ γ i)
    (hγ1 : ∑ i, γ i = 1) (a : Fin N) {C L lam δ : ℕ} (hδ : δ ≤ C) (hY : lam + δ ≤ L)
    {θ θ' : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) (hθ' : θ' ∈ Icc (0 : ℝ) 1) :
    |γ a * (∑ x ∈ range (lam + δ + 1), (x : ℝ) * pmf θ lam δ x
          - ∑ x ∈ range (lam + δ + 1), (x : ℝ) * pmf θ' lam δ x)|
      ≤ ((C : ℝ) ^ 2 / 2 + (C : ℝ) * (L : ℝ)) * |θ - θ'| := by
  show |γ a * (∑ x ∈ range (lam + δ + 1), (x : ℝ) * pmf θ lam δ x
          - ∑ x ∈ range (lam + δ + 1), (x : ℝ) * pmf θ' lam δ x)| ≤ _
  have hcoef := meanCoeff_le (C := C) (L := L) (lam := lam) (δ := δ) hδ hY
  have hmean := beliefMean_diff_le hθ hθ' lam δ
  have hγa := weight_le_one hγ0 hγ1 a
  rw [abs_mul, abs_of_nonneg (hγ0 a)]
  calc γ a * |∑ x ∈ range (lam + δ + 1), (x : ℝ) * pmf θ lam δ x
            - ∑ x ∈ range (lam + δ + 1), (x : ℝ) * pmf θ' lam δ x|
      ≤ 1 * (((δ : ℝ) * ((δ : ℝ) - 1) / 2 + (δ : ℝ) * ((lam : ℝ) + (δ : ℝ))) * |θ - θ'|) :=
        mul_le_mul hγa hmean (abs_nonneg _) zero_le_one
    _ ≤ ((C : ℝ) ^ 2 / 2 + (C : ℝ) * (L : ℝ)) * |θ - θ'| := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)

/-! ## Eq (37) — the value-function term -/

/-- **Eq (37).**  The second half of the Bellman difference: the state-transition term
`∑_x (P^{θ*}_x − P^{θ_l}_x)·J(H_{t−1} ∪ (A_t, x))`.

`J` is any value-function-shaped quantity bounded by `(C+D)·L` — in the paper,
`J^{θ_l}_{π_l,t+1}(H_{t−1})`, which is a sum of at most `L` future per-round penalties, each
of at most `C + D` by Lemma 6.  Eq (23) then gives the `2δ|θ* − θ_l| ≤ 2C|θ* − θ_l|` factor. -/
theorem stateTerm_le {lam δ C D L : ℕ} {J : ℕ → ℝ}
    (hδ : δ ≤ C) (hJ : ∀ x, |J x| ≤ ((C : ℝ) + (D : ℝ)) * (L : ℝ))
    {θ θ' : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) (hθ' : θ' ∈ Icc (0 : ℝ) 1) :
    |∑ x ∈ range (lam + δ + 1), (pmf θ lam δ x - pmf θ' lam δ x) * J x|
      ≤ 2 * (C : ℝ) * ((C : ℝ) + (D : ℝ)) * (L : ℝ) * |θ - θ'| := by
  show |∑ x ∈ range (lam + δ + 1), (pmf θ lam δ x - pmf θ' lam δ x) * J x| ≤ _
  have hδR : (δ : ℝ) ≤ (C : ℝ) := by exact_mod_cast hδ
  have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := Nat.cast_nonneg δ
  have hJ0 : 0 ≤ ((C : ℝ) + (D : ℝ)) * (L : ℝ) := by positivity
  have hl1 := l1_lipschitz θ θ' hθ hθ' lam δ
  have hterm : ∀ x ∈ range (lam + δ + 1),
      |(pmf θ lam δ x - pmf θ' lam δ x) * J x|
        ≤ |pmf θ lam δ x - pmf θ' lam δ x| * (((C : ℝ) + (D : ℝ)) * (L : ℝ)) := by
    intro x _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hJ x) (abs_nonneg _)
  calc |∑ x ∈ range (lam + δ + 1), (pmf θ lam δ x - pmf θ' lam δ x) * J x|
      ≤ ∑ x ∈ range (lam + δ + 1), |(pmf θ lam δ x - pmf θ' lam δ x) * J x| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ range (lam + δ + 1),
          |pmf θ lam δ x - pmf θ' lam δ x| * (((C : ℝ) + (D : ℝ)) * (L : ℝ)) :=
        sum_le_sum hterm
    _ = (∑ x ∈ range (lam + δ + 1), |pmf θ lam δ x - pmf θ' lam δ x| : ℝ)
          * (((C : ℝ) + (D : ℝ)) * (L : ℝ)) := by rw [sum_mul]
    _ ≤ (2 * (δ : ℝ) * |θ - θ'|) * (((C : ℝ) + (D : ℝ)) * (L : ℝ)) :=
        mul_le_mul_of_nonneg_right hl1 hJ0
    _ = (2 * |θ - θ'| * (((C : ℝ) + (D : ℝ)) * (L : ℝ))) * (δ : ℝ) := by ring
    _ ≤ (2 * |θ - θ'| * (((C : ℝ) + (D : ℝ)) * (L : ℝ))) * (C : ℝ) :=
        mul_le_mul_of_nonneg_left hδR (by positivity)
    _ = 2 * (C : ℝ) * ((C : ℝ) + (D : ℝ)) * (L : ℝ) * |θ - θ'| := by ring

/-! ## Eq (38) — the assembly across rounds and episodes -/

/-- **Eq (38), one episode.**  Lemma 4 of the paper — a result of [28] that the paper cites
rather than proves — decomposes an episode's regret into the sum over its `L` rounds of
Bellman differences `(T^{θ*}_{π_l} − T^{θ_l}_{π_l}) J^{θ_l}_{π_l,t+1}(H_{t−1})`.  Each such
difference is bounded by `K·δ_t` with `δ_t = |θ*_{A_t} − θ_l_{A_t}| ≥ 0`, which is exactly
Eq (36) plus Eq (37) with `K = ½C² + (2C² + 2CD + C)·L` (see `perRoundPenaltyDiff_le` and
`stateTerm_le`: `K = (½C² + LC) + 2C(C+D)L`).  Hence the episode's regret is at most `K`
times the episode's total divergence.

The sign is handled by the triangle inequality, not by an assumption on the sign of the
per-round differences; consequently the statement needs **no** hypothesis `K ≥ 0` and no
hypothesis `δ_t ≥ 0`.  (The coefficient `K` is nevertheless nonnegative in the paper — see
`regretCoeff_nonneg` in `TSDPP/Rate.lean`.) -/
theorem episodeRegret_le {L : ℕ} {K : ℝ} (regret : ℝ) (diff delta : ℕ → ℝ)
    (hregret : regret = ∑ t ∈ range L, diff t)
    (h : ∀ t, |diff t| ≤ K * delta t) :
    |regret| ≤ K * ∑ t ∈ range L, delta t := by
  show |regret| ≤ K * ∑ t ∈ range L, delta t
  subst hregret
  calc |∑ t ∈ range L, diff t| ≤ ∑ t ∈ range L, |diff t| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ range L, K * delta t := sum_le_sum fun t _ => h t
    _ = K * ∑ t ∈ range L, delta t := by rw [mul_sum]

/-- **Eq (38), across episodes.**  Summing the per-episode bound of `episodeRegret_le` over
the `m` episodes of the horizon gives the paper's Eq (38) shape: the Bayesian regret is at
most the per-round coefficient `K` times the total divergence
`Σ_l Σ_t |θ*_{A_t} − θ_l_{A_t}|`. -/
theorem regret_le {m L : ℕ} {K : ℝ} (episodeRegret : ℕ → ℝ) (delta : ℕ → ℕ → ℝ)
    (h : ∀ l, |episodeRegret l| ≤ K * ∑ t ∈ range L, delta l t) :
    |∑ l ∈ range m, episodeRegret l|
      ≤ K * ∑ l ∈ range m, ∑ t ∈ range L, delta l t := by
  show |∑ l ∈ range m, episodeRegret l| ≤ K * ∑ l ∈ range m, ∑ t ∈ range L, delta l t
  calc |∑ l ∈ range m, episodeRegret l| ≤ ∑ l ∈ range m, |episodeRegret l| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ l ∈ range m, K * (∑ t ∈ range L, delta l t) := sum_le_sum fun l _ => h l
    _ = K * ∑ l ∈ range m, ∑ t ∈ range L, delta l t := by rw [mul_sum]

end TSDPP
