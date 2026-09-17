/-
Copyright: formal artifact for INFOCOM'26 `infocom26.pdf`.
Released under Apache 2.0 license as described in the file LICENSE.

Root module: builds the whole formalization.  Module order follows the dependency DAG in
`cards/README.md`; every leaf below is `sorry`-free, `axiom`-free and free of
`native_decide`/`unsafe`/floats.
-/
import TSDPP.Basic
import TSDPP.Ineq
import TSDPP.Belief
import TSDPP.Model
import TSDPP.Lipschitz
import TSDPP.StateBound
import TSDPP.Conjugacy
import TSDPP.Decomp
import TSDPP.Regret
import TSDPP.Simulation
import TSDPP.Assembly
import TSDPP.Tail
import TSDPP.Rate
import TSDPP.Theorem2
import TSDPP.Asymptotic
-- Lemma 5 (Beta concentration) support.  These two were previously outside the import closure,
-- which meant they were built by nothing and scanned by nothing — the same "present in the tree,
-- absent from CI" hole as the peer's non-recursive `scan_forbidden.py` glob.  `KL` is the
-- Chernoff/klog inequality used by the rate arithmetic; `GammaMGF` supplies
-- `gammaMeasure_lintegral_exp`, the `(1-λ)^{-α}` step of the one-sample Beta tail bound.
import TSDPP.KL
import TSDPP.GammaMGF
-- Lemma 5's remaining support, added when it was promoted out of `Scratch/`.  `BetaGamma` was
-- already outside the closure before that — the same hole again, and it is the 516-line
-- closed ratio law that the whole `c₀ = 11/100` route rests on, so it was the worst one to have
-- been invisible to `lake build` and to `scan_forbidden.py`.
import TSDPP.BetaGamma
import TSDPP.BetaGammaChernoff
import TSDPP.UnionBound
-- The map-level ratio law, welding the set-level law above to the two one-sample tails.  This is
-- the `hmap` hypothesis that `BetaGammaChernoff`'s two tails take; with it in the closure, that
-- hypothesis becomes dischargeable from the tree rather than assumed.
import TSDPP.GammaRatioMap
-- Lemma 5's concentration module itself — the last module that was *in the tree but in no closure*.
-- It was the one `IN_FLIGHT` exemption in `scripts/check_axioms.sh`: imported by nothing, so
-- `lake build TSDPP` never compiled it and `Audit.lean` (which imports only `TSDPP`) could not even
-- resolve its names, leaving its twelve public declarations axiom-unaudited.  The exemption is
-- deleted and the module is wired in here; `scripts/check_axioms.sh` now *requires* every module in
-- this closure to be represented in `Audit.lean`, so it cannot come back.
--
-- Wiring it in closes no mathematical gap.  The target
-- `Pr(|X-Y| ≥ r·α/(α+β)) ≤ 2·exp(-(11/100)·α·r²)` is still NOT proved: `unionWitness_explicit`
-- reduces it to the explicitly undischarged `hnum` (see `DESIGN.md` GAP-2b and trap P-62), so what
-- the new `#print axioms` lines audit is the *reduction*, not the target.  Its nine `private`
-- helpers are file-scoped in Lean 4 and cannot be named from `Audit.lean`.
import TSDPP.BetaConcentration
-- The machine-checked refutation of the registered Lemma 5 target, plus the `Beta(1,B)` closed-form
-- tail it rests on.  This is the artifact's answer to `CLAUDE.md` item 1 ("完整证明**或反证**"):
-- `lemma5_as_registered_is_false` and `paper_lemma5_range_ge_one_is_false` are unconditional.
-- Note the SCOPE banner in `Lemma5Refutation.lean`: the `r ≥ 1` statement is refuted, the paper's
-- own Lemma 5 (stated for `0 ≤ r ≤ 1`) is not, and neither is the paper's theorem.
import TSDPP.BetaOneCDF
import TSDPP.Lemma5Refutation
