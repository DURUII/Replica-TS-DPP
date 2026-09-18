/-
Copyright: formal artifact for INFOCOM'26 `infocom26.pdf`.
Released under Apache 2.0 license as described in the file LICENSE.

# Axiom audit

`CLAUDE.md` forbids closing a goal with an axiom, `native_decide`, `unsafe` or floats.  This
file is the machine-checkable part of that promise: for every headline theorem it prints the
axioms the declaration actually depends on.  Every line must read exactly

  `'TSDPP.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]`

and in particular must never mention `sorryAx`.  `lean4/scripts/check_axioms.sh` greps the
output of `lake env lean TSDPP/Audit.lean` and fails if any line deviates.

Note this file is deliberately **not** imported by `TSDPP.lean`: `#print axioms` is a command,
not a declaration, so importing it from the root module would put audit output in every build.
-/
import TSDPP
#print axioms TSDPP.sum_range_inv_sqrt_le
#print axioms TSDPP.sum_inv_sqrt_weighted
#print axioms TSDPP.l1_lipschitz
#print axioms TSDPP.firstMoment_lipschitz
#print axioms TSDPP.pmf_sum_one
#print axioms TSDPP.pmf_mean
#print axioms TSDPP.tail_le_eps
#print axioms TSDPP.chainPMF_sum_one
#print axioms TSDPP.copyStep_iterate
#print axioms TSDPP.penalty_identity
#print axioms TSDPP.penalty_diff
#print axioms TSDPP.bestArm_spec
#print axioms TSDPP.lintegral_conj
#print axioms TSDPP.betaPDFReal_conj
#print axioms TSDPP.pow_add_weighted_le_one
#print axioms TSDPP.succ_mul_pow_sub_le_one

-- R9, analytic core of Lemma 2 (Eq (25)): the two Bernoulli corollaries are spent here.
#print axioms TSDPP.arm_deriv_abs_le_one
#print axioms TSDPP.armTerm_lipschitz
#print axioms TSDPP.atomTerm_lipschitz

-- R1, used by Lemma 6 to turn "never resets" into `(1-θ)^d`.
#print axioms TSDPP.chain_path_no_reset

-- Coverage table in `FIDELITY.md` §1.0: Definitions 2–4 and Lemma 1, plus the remaining
-- Theorem 1 forms.  These are cited there as *closed*, so they are audited here too.
#print axioms TSDPP.copyStep
#print axioms TSDPP.copyStep_self
#print axioms TSDPP.copyStep_other
#print axioms TSDPP.bestArm
#print axioms TSDPP.bestArm_congr
#print axioms TSDPP.betaPDFReal_conj_all
#print axioms TSDPP.betaPDFReal_conj_ratio
#print axioms TSDPP.conjWeight_nonneg

-- R10 / R11 — Eq (36), (37), (38).
#print axioms TSDPP.beliefMean_diff_le
#print axioms TSDPP.perRoundPenaltyDiff_le
#print axioms TSDPP.stateTerm_le
#print axioms TSDPP.episodeRegret_le
#print axioms TSDPP.regret_le

-- R13 — Eq (40), the geometric tail.
#print axioms TSDPP.geom_exp_sum_le
#print axioms TSDPP.tail_sum_le

-- R16 — Theorem 2's final rate arithmetic.
#print axioms TSDPP.mul_sqrt_eq_sqrt_sq_mul
#print axioms TSDPP.two_mul_sqrt_ratio_le
#print axioms TSDPP.rate_core

-- ROOT — Theorem 2, assembled.  These are the headline declarations.
#print axioms TSDPP.eq39_collapse
#print axioms TSDPP.theorem2_withTail
#print axioms TSDPP.theorem2_concrete
#print axioms TSDPP.regretCoeff_le_mul
-- Referenced by `Regret.lean`'s docstring for `episodeRegret_le`; it did not exist until the
-- dangling reference was fixed.
#print axioms TSDPP.regretCoeff_nonneg
#print axioms TSDPP.theorem2_rate

-- L3 — Lemma 3, discharged: the `hdecomp` hypothesis of `theorem2_rate` is now *derived*.
#print axioms TSDPP.sum_range_blocks
#print axioms TSDPP.regret_decomp
#print axioms TSDPP.episodeOf
#print axioms TSDPP.regret_decomp_episodeOf
#print axioms TSDPP.theorem3_rate

-- Asymp — Theorem 2's `O(·)`, formalized rather than left as notation (GAP-4's convention).
#print axioms TSDPP.sqrt_L3TlogT_isTheta
#print axioms TSDPP.bound_isBigO_sqrt_log
#print axioms TSDPP.bound_isBigO_in_episodes

-- L4 — Lemma 4, PROVED but NOT INSTANTIATED.  Its mathematical content is derived, not assumed:
-- `simulation_lemma` is Eq (30)'s telescoping, and `bellman_step_le` supplies its `hrec`,
-- identifying `g t` as the Bellman-operator difference.  But it is stated over an ARBITRARY
-- probability space — there is no bandit content in it — and the instantiation to the model is
-- missing: `Theorem2.lean` does NOT import `Simulation`, and `hper` remains a *hypothesis* of
-- BOTH `theorem2_rate` and `theorem3_rate`.  Blocked on GAP-7 (the trajectory law P_{θ*} and the
-- posterior samplings Q^l), not on R4.  Do not read the two `#print axioms` lines below as
-- evidence that `hper` has been discharged from the two theorems — they are not.
-- (Wording corrected; this previously said "discharged", which over-claimed in the same way
-- `cards/README.md` did.  See DESIGN.md trap P-51.)
#print axioms TSDPP.simulation_lemma
#print axioms TSDPP.bellman_step_le

-- L5 support — these are the *ingredients* of Lemma 5 (Beta concentration), plus the Beta–Gamma
-- ratio law (`TSDPP.gamma_ratio_isBetaMeasure`) and the two-case union-bound witness
-- (`TSDPP.unionWitness`).  They do NOT add up to Lemma 5: the target
-- `Pr(|X-Y| ≥ r·α/(α+β)) ≤ 2·exp(-(11/100)·α·r²)` is NOT proved anywhere in the closure — and, as
-- registered (on `r ≥ 1`), it is **FALSE**: see the P-64 note below before reading anything here as
-- a statement of progress.  Everything in `TSDPP/BetaConcentration.lean` reduces it to the explicit residual
-- hypothesis `hnum`, which is undischarged.  That module *was* the one `IN_FLIGHT` exemption in
-- `scripts/check_axioms.sh` — which meant neither the orphan check nor this file ever looked at it —
-- and it now has its own section at the end of this file.  Note that auditing its declarations does
-- NOT advance the status sentence above: what is audited is the reduction to `hnum`, not the target.
-- The obstruction is method-level, and the union-bound route is not known to bound either
-- variable: the ceiling on `r` (`r ≤ 1.058737`) that stood here is [RETRACTED — 该替换使用了对称切片
-- 的一维下界,对 `hnum` 无效]; see `DESIGN.md` GAP-2b and traps P-62/P-63.  What survives is only
-- that `hnum` is satisfiable for every `r ≥ 1` — and that the satisfying witnesses all sit at event
-- level `s = r/(1+ρ) → 1`, where `Pr(|X-Y| ≥ s)` is nearly empty (P-63: the collapse set `ρ ≤ r-1`
-- and the empty-event set `r ≥ 1+ρ` are the same inequality).  So this is *not* a claim that the
-- union-bound method is strong at large `r`; whatever ceiling exists is bought with vacuity.
--
-- [2026-09-17 — trap P-64: "satisfiable" above must NOT be read as "the bound is fine".]  The
-- registered target is FALSE on `r ≥ 1`: at `(α,β,r) = (2,200,10)` the exact probability is
-- 8.6066e−09 against a bound of `2e^{−22} = 2.7895e−10`.  The two statements are consistent —
-- `hnum` is satisfiable only in the vacuous region `ρ ≤ r-1`, and `ρ = 100` is far outside it —
-- but the wording above ("satisfiable for every r ≥ 1") is exactly the kind of sentence that reads
-- as a positive status report, and it is not one.  Outside the vacuous region the antecedent is
-- *unsatisfiable* on `r ≥ 1` (a 2305× miss at the best admissible split, `δ₁ = r−1`, `δ → 0`, so
-- the method's range and the paper's range have disjoint interiors).  The paper's own range
-- `0 ≤ r ≤ 1` is where the lemma is true, but it is unreachable from this toolkit: the union split
-- requires `r ≥ 1`, and the Gamma-Markov one-sample bound degenerates to 1 at or below the mean.
-- Full record: `DESIGN.md` P-64, `FIDELITY.md` §3.4, `cards/L5.md`, and the header of
-- `TSDPP/BetaConcentration.lean`.
--
-- [2026-09-17 — trap P-67: the P-64 witnesses are not the worst case.]  P-64's witnesses sit at
-- `r = 10`, `ρ = 100` — outside the vacuous region, but **off the curve Eq (33) prescribes**
-- (`r = max{1, √(8 log T/α)}`).  On that curve the **paper's own `1/8` fails too**, in 5 of 6 sampled
-- tuples, including `α = 1, T = 10⁶` (`c_eff = 0.11182 < 0.125`).  So the artifact's registered
-- bound is not merely false as formalized; the paper's *use* of Lemma 5 is false on the paper's own
-- settings.  `c_eff` decreases in `r` sub-quadratically (the log-density is near-linear in the
-- deviation past the CLT region), so small `α` — which Eq (33) gives large `r` — is the dangerous
-- corner.  Nothing in this audit file changes: `hnum ⟹ bound` is still a theorem.
-- `gammaMeasure_lintegral_exp` is the load-bearing one: it supplies the Gamma Laplace transform
-- `(1-λ)^{-α}` that the one-sample Beta tail bound needs, and it is why Lemma 5 does NOT require a
-- confluent hypergeometric function (see `DESIGN.md` GAP-2c — the absence of `₁F₁` is why the
-- one-sample tails here are Markov/Chernoff rather than exact).
--
-- [P-64 correction to that last clause.]  It previously read "… the paper's constant `1/8` is
-- unreachable by this method and `11/100` is used instead", which frames the gap as a *constant*
-- problem.  It is not: the operative difference between the paper's Lemma 5 and this module is the
-- **range** (`0 ≤ r ≤ 1` vs `r ≥ 1`).  The paper's `1/8` is not refuted on its own range, and the
-- artifact's `11/100` is not merely weaker — it is false on the range this module quantifies over.
-- Tracing `11/100` back to a "1/8 is unreachable" ceiling would be tracing it to a retracted
-- argument (P-62 layer 3, `c₀ = 11/100` is [UNDERIVED]).
#print axioms TSDPP.measurable_gammaPDF
#print axioms TSDPP.gammaMeasure_lintegral_exp
#print axioms TSDPP.cdf_gammaMeasure_eq_setLIntegral
#print axioms TSDPP.kl_chernoff_lower

-- L5 support, continued — the Beta–Gamma ratio law (`BetaGamma.lean`, closed) and the two
-- promoted modules (`BetaGammaChernoff.lean`, `UnionBound.lean`).  These were previously outside
-- the root import closure, so nothing built them and nothing scanned them; they are audited here
-- from the moment they entered `TSDPP/`.
#print axioms TSDPP.gammaMeasure_prod_ratio
#print axioms TSDPP.gammaMeasure_prod_lintegral_exp
#print axioms TSDPP.gammaMeasure_prod_meas_le
#print axioms TSDPP.gammaMeasure_apply_Iio_zero
#print axioms TSDPP.betaMeasure_Ici_le
#print axioms TSDPP.betaMeasure_Iio_le
#print axioms TSDPP.unionWitness

-- The map-level ratio law.  This is what turns the two one-sample tails' `hmap`
-- hypothesis from an assumption into something dischargeable from the tree.
#print axioms TSDPP.gamma_ratio_isBetaMeasure
-- A public global instance added by that file, needed so `Measure.prod_prod` fires.  Audited
-- because it is exported to the whole project, not just to its own module.
#print axioms TSDPP.instSFiniteGammaMeasure

-- L5, the module itself: `TSDPP/BetaConcentration.lean`, now imported by `TSDPP.lean`.  This is the
-- section that the old `IN_FLIGHT` exemption made impossible — the module was outside the root
-- closure, so `Audit.lean` (which imports only `TSDPP`) could not resolve these names at all, and
-- twelve public declarations were compiled by nothing and checked by nothing.  Wired in, exemption
-- deleted; `scripts/check_axioms.sh` now *requires* every closure module to be represented here.
--
-- The module's nine helpers (`rpow_beta_eq`, `numA'`, `numB'`, …) are `private`, i.e. file-scoped in
-- Lean 4: their mangled names are not importable, so they cannot be named here and are not audited.
-- Two of them are verbatim copies of `TSDPP/UnionBound.lean` private lemmas (see that file's
-- docstring), which is why `unionWitness` and `unionWitness_explicit` carry separate proofs.
--
-- `chernoffA`/`chernoffB` are the exact Chernoff optimisers `A(δ)`, `B(δ)`; auditing a `def` checks
-- the axioms of its *value*, not of a proof, and they are here because they are the whole content of
-- the two one-sample tails.
#print axioms TSDPP.chernoffA
#print axioms TSDPP.chernoffB
#print axioms TSDPP.unionWitness_explicit
#print axioms TSDPP.betaMeasure_Ici_chernoff
#print axioms TSDPP.betaMeasure_Iio_chernoff
#print axioms TSDPP.betaMeasure_prod_abs_sub_le_small
#print axioms TSDPP.betaMeasure_prod_abs_sub_le_union
#print axioms TSDPP.betaMeasure_prod_abs_sub_le_unionTail

-- The four `'`-suffixed forms: the same results with the `hmap` hypothesis discharged from
-- `TSDPP.gamma_ratio_isBetaMeasure`.  They are audited separately rather than assumed equal to the
-- primed-free ones above, since discharging `hmap` is a real proof step (`Measure.map` bookkeeping),
-- not a rename.  Note a trailing `'` is part of the *name*: `#print axioms` echoes it as
-- `'TSDPP.betaMeasure_Ici_chernoff'' depends on axioms: [...]`, which is why the reporting regex in
-- `scripts/check_axioms.sh` must admit `'` in a name (it previously did not, and silently filed
-- every primed name under "EMPTY axiom set").
#print axioms TSDPP.betaMeasure_Ici_chernoff'
#print axioms TSDPP.betaMeasure_Iio_chernoff'
#print axioms TSDPP.betaMeasure_prod_abs_sub_le_small'
#print axioms TSDPP.betaMeasure_prod_abs_sub_le_unionTail'

-- ---------------------------------------------------------------------------------------------
-- THE REFUTATION — `TSDPP/Lemma5Refutation.lean` and its analytic input `TSDPP/BetaOneCDF.lean`
-- ---------------------------------------------------------------------------------------------
--
-- These eleven declarations are the *deliverable* under `CLAUDE.md` item 1's "完整证明**或反证**".
-- The registered Lemma 5 target is false on `r ≥ 1`, and unlike the `BetaConcentration.lean` block
-- above — which audits a *reduction* to the undischarged `hnum` — these are unconditional: no
-- hypotheses, no residual, no open sub-node.  `lemma5_as_registered_is_false` and
-- `paper_lemma5_range_ge_one_is_false` are the two instances that matter (the artifact's `11/100`
-- and the paper's own `1/8`).
--
-- **SCOPE, and it is not a formality.**  What is refuted is the `r ≥ 1` statement — the one this
-- artifact registered.  The paper states its Lemma 5 for `0 ≤ r ≤ 1` (`paper.pdf` p. 9 Eq (31)),
-- and the witness sits at `r = 14`, outside that range, so the paper's own Lemma 5 is NOT refuted
-- here; nor is the paper's theorem, since a proof step that does not go through does not make a
-- theorem false.  See the header of `TSDPP/Lemma5Refutation.lean` and `cards/L5-REFUTATION.md` §0.
#print axioms TSDPP.pow_100_101_le
#print axioms TSDPP.exp_neg_le_pow_86_101
#print axioms TSDPP.arith_core
#print axioms TSDPP.refute_arith
#print axioms TSDPP.prod_Ici_prod_Iic_le_abs_sub
#print axioms TSDPP.betaMeasure_one_Ioo
#print axioms TSDPP.betaMeasure_one_Ici
#print axioms TSDPP.betaMeasure_one_Iic
#print axioms TSDPP.lemma5_range_ge_one_is_false
#print axioms TSDPP.lemma5_as_registered_is_false
#print axioms TSDPP.paper_lemma5_range_ge_one_is_false

-- ---------------------------------------------------------------------------------------------
-- THE PAPER'S OWN LEMMA 5, REDUCED — `TSDPP/Lemma5PaperRange.lean`
-- ---------------------------------------------------------------------------------------------
--
-- Complementary to the block above, and easy to confuse with it.  `Lemma5Refutation.lean` *refutes*
-- the registered statement on `r ≥ 1`; this module works the paper's own range `0 ≤ r ≤ 1`
-- (`paper.pdf` p. 9 Eq (31)) and does **not** close it.  `betaMeasure_prod_abs_sub_le_of_mgf` is
-- conditional on `BetaProdMGFBound` — a `def … : Prop` carried as an explicit hypothesis, never an
-- axiom — so what is audited here is a *reduction*, exactly as in the `BetaConcentration` block.
-- `betaMeasure_prod_abs_sub_le_of_log2` is unconditional but covers only `α r² ≤ 8 log 2`, where the
-- claimed bound is `≥ 1`, so it follows from `ν S ≤ ν univ = 1` and needs no analytic input.
--
-- The reduction spends no slack: Markov at `λ := r(α+β)/4` gives `2αλ²/(α+β)² = αr²/8` and
-- `λrμ = αr²/4`, so the exponent is exactly `−αr²/8`.  The MGF bound's own hypothesis
-- `λ ≤ (α+β)/4` is, at that `λ`, exactly `r ≤ 1` — the paper's range restriction is the validity
-- range of its own optimal tilt, which is why the range and the constant are what they are.
--
-- Residual `BetaProdMGFBound α β` is unproved; its global sup is `16/9 < 2`, approached only at
-- `α → 0, β → ∞, u = (α+β)/4`, so no inequality with slack closes it.  `DESIGN.md` GAP-2.
#print axioms TSDPP.BetaProdMGFBound
#print axioms TSDPP.betaMeasure_prod_abs_sub_le_of_log2
#print axioms TSDPP.betaMeasure_prod_abs_sub_le_of_mgf
