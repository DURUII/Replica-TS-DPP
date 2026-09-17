/-
Copyright: formal artifact for INFOCOM'26 `infocom26.pdf`.
Released under Apache 2.0 license as described in the file LICENSE.

# L4 — Lemma 4, the Bellman decomposition, no longer a hypothesis

The paper's Lemma 4 (Eq (30)) is

  `J^{θ*}_{π^l,1}(H_0) − J^{θ^l}_{π^l,1}(H_0)`
    `= E_{θ*,π^l}[ Σ_{t=1}^{L} (T^{θ*}_{π^l} − T^{θ^l}_{π^l}) J^{θ^l}_{π^l,t+1}(H_{t−1}) ]`.

`Regret.episodeRegret_le` consumes exactly this, in the form
`regret = ∑ t ∈ range L, diff t` with `diff t` the per-round Bellman difference.  Up to now that
was a *hypothesis*.  This module proves it.

## What the identity actually is

Strip away the bandit vocabulary and Eq (30) says: **a difference of value functions is the sum
of its per-round increments, and the per-round increment is the Bellman-operator difference.**

Concretely, put `ΔJ t = J^{θ*}_t − J^{θ^l}_t` on the trajectory and let `F t` be the σ-algebra of
the history `H_{t−1}`.  Then

  `E_μ[ ΔJ t − ΔJ (t+1) | F t ] = (T^{θ*} − T^{θ^l}) J^{θ^l}_{t+1}(H_{t−1})`,

and summing over `t = 0, …, L−1` telescopes, because `ΔJ L = 0` (the value function is zero at the
horizon).

That telescoping is `simulation_lemma` below, stated for an arbitrary filtered probability space,
an arbitrary `ΔJ` and an arbitrary `g`.  It is the classical "simulation lemma" of the reinforcement
learning literature and is the whole of Lemma 4's probabilistic content.  Note what it does *not*
mention: no bandit, no Beta posterior, no AoI.  The bandit enters only through `bellman_step_le`
further down, which discharges `hrec` from the two Bellman recursions.

## Why this is the honest discharge, and where the residue is

`simulation_lemma` needs two things the paper gets for free and this file therefore isolates:

* `hmeas` — `ΔJ` is adapted, `ΔJ (t+1)` being `F t`-measurable.  In the paper this is the statement
  that the value function at round `t+1` is determined by `H_t`, which is *how `J` is defined*.
* `hrec` — the per-round Bellman difference, which `bellman_step_le` derives from the two value
  recursions.

What remains outside the formalization is the construction of the filtered space itself: the
trajectory law `P_{θ*}` and the posterior samplings `θ^l ∼ Q^l`.  That is hypothesis `hdecomp`'s
cousin in `Theorem2`, and it is where `BR` still enters as an explicit function rather than a
defined quantity — see `DESIGN.md` GAP-7.

## Card

DAG node L4.  Depends on: none (pure `MeasureTheory`, plus `TSDPP.Regret` for the shape it feeds).
Discharges the `hregret` premise of `Regret.episodeRegret_le` and, through it, part of `hper` in
`Theorem2.theorem2_concrete`.
-/
import Mathlib
import TSDPP.Regret

namespace TSDPP

open MeasureTheory Finset

/-- **Lemma 4 (Eq (30)), the telescoping core.**  Let `F` be a filtration, `ΔJ` an adapted process
of integrable random variables with `ΔJ L = 0`, and `g` a process satisfying the per-round Bellman
identity `E[ΔJ t − ΔJ (t+1) | F t] = g t`.  Then the total is the sum of the per-round pieces:

  `∫ ΔJ 0 = Σ_{t<L} ∫ g t`.

The proof is two lines of substance.  Each summand is
`∫ΔJ t − ∫ΔJ (t+1) = ∫(ΔJ t − ΔJ (t+1)) = ∫ E[ΔJ t − ΔJ (t+1) | F t] = ∫ g t`, the middle
step being `integral_condExp`; and `∑_{t<L}(a t − a (t+1)) = a 0 − a L` is
`Finset.sum_range_sub'`.  Nothing here is specific to bandits.

The hypotheses are deliberately the *weakest* form: no `g`-integrability is needed, because `g` is
never integrated on its own — it is only ever reached through an almost-everywhere rewrite. -/
theorem simulation_lemma {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (hF : ∀ t, F t ≤ ‹MeasurableSpace Ω›)
    (ΔJ : ℕ → Ω → ℝ) (g : ℕ → Ω → ℝ) (L : ℕ)
    (hint : ∀ t, Integrable (ΔJ t) μ)
    (hrec : ∀ t, t < L → μ[ΔJ t - ΔJ (t + 1) | F t] =ᵐ[μ] g t)
    (hL : ΔJ L = 0) :
    ∫ ω, ΔJ 0 ω ∂μ = ∑ t ∈ range L, ∫ ω, g t ω ∂μ := by
  show ∫ ω, ΔJ 0 ω ∂μ = ∑ t ∈ range L, ∫ ω, g t ω ∂μ
  -- Each round contributes `∫g t`.
  have hstep : ∀ t, t < L →
      ∫ ω, ΔJ t ω ∂μ - ∫ ω, ΔJ (t + 1) ω ∂μ = ∫ ω, g t ω ∂μ := by
    intro t ht
    show ∫ ω, ΔJ t ω ∂μ - ∫ ω, ΔJ (t + 1) ω ∂μ = ∫ ω, g t ω ∂μ
    rw [← integral_sub (hint t) (hint (t + 1))]
    rw [← integral_condExp (hF t)]
    exact integral_congr_ae (hrec t ht)
  -- The increments telescope.
  have htel : ∑ t ∈ range L, (∫ ω, ΔJ t ω ∂μ - ∫ ω, ΔJ (t + 1) ω ∂μ)
      = ∫ ω, ΔJ 0 ω ∂μ := by
    show ∑ t ∈ range L, (_) = ∫ ω, ΔJ 0 ω ∂μ
    rw [sum_range_sub']
    simp [hL]
  calc ∫ ω, ΔJ 0 ω ∂μ
      = ∑ t ∈ range L, (∫ ω, ΔJ t ω ∂μ - ∫ ω, ΔJ (t + 1) ω ∂μ) := htel.symm
    _ = ∑ t ∈ range L, ∫ ω, g t ω ∂μ :=
        sum_congr rfl fun t ht => hstep t (mem_range.mp ht)

/-- **Where `hrec` comes from: the Bellman step.**  `simulation_lemma` above assumed the per-round
identity `E_μ[ΔJ t − ΔJ (t+1) | F t] = g t`.  This theorem *derives* it from the two value
recursions, and identifies `g t` as the Bellman-operator difference of Eq (30):

  `g t = E_μ[r t + J^ν_{t+1} | F t] − E_ν[r t + J^ν_{t+1} | F t]`.

The two measures are the trajectory laws: `μ = P_{θ*}` (the environment actually played) and
`ν = P_{θ_l}` (the parameter the policy believes).  `J^μ` obeys its recursion under `μ`, `J^ν`
under `ν`; `r` is the *same* random variable on `Ω` in both cases, which is why the difference of
the two recursions leaves only the operator gap.

## Why `μ ≪ ν` is carried

`J^ν t =ᵐ[ν] ν[r t + J^ν_{t+1} | F t]` is a statement about the `ν`-null sets, but it is consumed
under `μ` (everything on the left of the conclusion is `μ`-a.e.).  `Measure.AbsolutelyContinuous.ae_eq`
is the bridge, and it needs `μ ≪ ν` — *not* the converse.  The direction matters and is easy to get
backwards: `μ ≪ ν` says `ν`-null implies `μ`-null, which is what promotes a `ν`-a.e. identity to a
`μ`-a.e. one.  (`ν ≪ μ` would give the opposite, and is not what is used.)  In the paper's setting
this is free either way: for a finite horizon and `θ*, θ_l ∈ (0,1)` the likelihood ratio is a.s.
finite and positive, so the two trajectory laws are mutually absolutely continuous.

## The side conditions, honestly

`hintJμ`, `hintJνμ`, `hintrμ` are `μ`-integrability; `hintJνν`, `hintrν` are `ν`-integrability.
Both are needed because `condExp_add`/`condExp_sub` are stated for integrable functions, and
`hJμa`/`hJνa` are the adaptedness of the value functions — in the paper, *how `J` is defined*
(`J^θ_{π,t}` depends only on `H_{t−1}`).  No hypothesis here is about bandits; all are the
elementary regularity that makes the conditional expectations well behaved. -/
theorem bellman_step_le {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω} [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (hF : ∀ t, F t ≤ ‹MeasurableSpace Ω›)
    (hμν : μ ≪ ν) (r Jμ Jν : ℕ → Ω → ℝ) (t : ℕ)
    (hintJμ : ∀ s, Integrable (Jμ s) μ)
    (hintJνμ : ∀ s, Integrable (Jν s) μ)
    (hintJνν : ∀ s, Integrable (Jν s) ν)
    (hintrμ : Integrable (r t) μ) (hintrν : Integrable (r t) ν)
    (hJμa : StronglyMeasurable[F t] (Jμ t))
    (hJνa : StronglyMeasurable[F t] (Jν t))
    (hμbell : Jμ t =ᵐ[μ] μ[r t + Jμ (t + 1) | F t])
    (hνbell : Jν t =ᵐ[ν] ν[r t + Jν (t + 1) | F t]) :
    μ[(Jμ t - Jν t) - (Jμ (t + 1) - Jν (t + 1)) | F t]
      =ᵐ[μ] μ[r t + Jν (t + 1) | F t] - ν[r t + Jν (t + 1) | F t] := by
  show μ[(Jμ t - Jν t) - (Jμ (t + 1) - Jν (t + 1)) | F t]
      =ᵐ[μ] μ[r t + Jν (t + 1) | F t] - ν[r t + Jν (t + 1) | F t]
  -- Split the conditional expectation of the increment into four pieces.
  have hA : μ[(Jμ t - Jν t) - (Jμ (t + 1) - Jν (t + 1)) | F t]
      =ᵐ[μ] μ[Jμ t - Jν t | F t] - μ[Jμ (t + 1) - Jν (t + 1) | F t] :=
    condExp_sub ((hintJμ t).sub (hintJνμ t)) ((hintJμ (t + 1)).sub (hintJνμ (t + 1))) (F t)
  have hB : μ[Jμ t - Jν t | F t] =ᵐ[μ] μ[Jμ t | F t] - μ[Jν t | F t] :=
    condExp_sub (hintJμ t) (hintJνμ t) (F t)
  have hC : μ[Jμ (t + 1) - Jν (t + 1) | F t] =ᵐ[μ] μ[Jμ (t + 1) | F t] - μ[Jν (t + 1) | F t] :=
    condExp_sub (hintJμ (t + 1)) (hintJνμ (t + 1)) (F t)
  -- The value functions are `F t`-measurable, so conditioning fixes them.
  have hD : μ[Jμ t | F t] =ᵐ[μ] Jμ t :=
    Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable (hF t) hJμa (hintJμ t))
  have hE : μ[Jν t | F t] =ᵐ[μ] Jν t :=
    Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable (hF t) hJνa (hintJνμ t))
  -- Both recursions, split by additivity of the conditional expectation.
  have hSpμ : μ[r t + Jμ (t + 1) | F t] =ᵐ[μ] μ[r t | F t] + μ[Jμ (t + 1) | F t] :=
    condExp_add hintrμ (hintJμ (t + 1)) (F t)
  have hSpμν : μ[r t + Jν (t + 1) | F t] =ᵐ[μ] μ[r t | F t] + μ[Jν (t + 1) | F t] :=
    condExp_add hintrμ (hintJνμ (t + 1)) (F t)
  have hSpν : ν[r t + Jν (t + 1) | F t] =ᵐ[ν] ν[r t | F t] + ν[Jν (t + 1) | F t] :=
    condExp_add hintrν (hintJνν (t + 1)) (F t)
  -- `hSpν` and `hνbell` live under `ν`; move both to `μ`.
  have hSpν' : ν[r t + Jν (t + 1) | F t] =ᵐ[μ] ν[r t | F t] + ν[Jν (t + 1) | F t] :=
    hμν.ae_eq hSpν
  have hνbell' : Jν t =ᵐ[μ] ν[r t + Jν (t + 1) | F t] := hμν.ae_eq hνbell
  filter_upwards [hA, hB, hC, hD, hE, hSpμ, hSpμν, hSpν', hνbell', hμbell] with
    ω eA eB eC eD eE eSpμ eSpμν eSpν eνbell eμbell
  -- Peel the pointwise `+`/`−` on functions so that `linarith` sees plain real equations.
  simp only [Pi.sub_apply, Pi.add_apply] at *
  linarith

end TSDPP
