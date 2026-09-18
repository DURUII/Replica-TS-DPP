# TS-DPP — the Lean 4 formalization of *Age-of-Information-Aware Mobile Crowdsensing for Uncertain Event Capture* (INFOCOM'26)

English | [中文](README.zh.md)

> Lean `v4.35.0-rc2`, mathlib4 `f61f3ed7633ff99ecaae4a086395b501652a76ee`, project at `lean4/`.
> The root module `TSDPP.lean` reaches 25 modules; `TSDPP/*.lean` totals 5,102 lines.

## Overview

```
@inproceedings{zhou2026age,
  title={Age-of-Information-Aware Mobile Crowdsensing for Uncertain Event Capture},
  author={Zhou, Jinrui and Xu, Yin and Xu, Haotian and Xiao, Mingjun and Wu, Jie},
  booktitle={IEEE INFOCOM 2026 - IEEE Conference on Computer Communications},
  pages={1--10},
  year={2026},
  organization={IEEE},
  doi={10.1109/INFOCOM59046.2026.11571737}
}
```

The paper models uncertain event capture as a constrained episodic restless bandit with an unknown
transition probability, and proposes **TS-DPP**: a belief-Drift-Plus-Penalty bandit policy combined
with Thompson sampling. Its headline theoretical claim is **Theorem 2** (§IV, Eq (19)):

> The Bayesian regret satisfies `BR(T) = O( √(L³ · T · log T) )`,
> where `T = m·L` is the horizon and `L` the episode length.

`CLAUDE.md` asks for two independent deliverables, a non-formal proof or refutation and a Lean 4
formalization of it, and permits no claim of success until both have passed independent
verification. This repository is that pair, together with the record of every route that did not
close. The replay of the paper's own experiments is a third, separate deliverable and lives in
[code/README.md](code/README.md).

## The result

Every **CLOSED** row below is a machine-checked declaration in the root module's import closure: the
row counts as closed only when its declaration builds with no `sorry` and its `#print axioms`
output is a subset of `{propext, Classical.choice, Quot.sound}`, which
`lean4/scripts/check_axioms.sh` fails the build over if any audited declaration deviates. The rows
that are not closed name what the artifact does not prove, and they carry no audited declaration of
their own.

| item | status | declaration |
| --- | --- | --- |
| Theorem 2, Eq (19), assembled (**ROOT**) | CLOSED | `theorem2_rate`, `theorem2_concrete`, `theorem2_withTail`, `eq39_collapse` |
| the 15 cards below the root in the DAG | CLOSED | `cards/README.md` carries the per-card table |
| the Gamma-ratio law behind Lemma 5 | CLOSED | `gammaMeasure_prod_ratio` |
| the registered Lemma 5 target, on `r ≥ 1` | **REFUTED, unconditional** | `lemma5_as_registered_is_false`, `paper_lemma5_range_ge_one_is_false` |
| the paper's problem statement, Eq (5)–(7), (10)–(14), (17), (18), (20)–(21) | NOT FORMALIZED | `cards/R4.md` |
| the paper's Lemma 3 and Lemma 4, quoted from [28] | hypotheses, never axioms | `hdecomp`, `hper` in `Theorem2.lean` |
| Corollary 1's radius and drift floors, quoted from [45] | hypotheses, never axioms | `hdelta`, `hηl` in `Theorem2.lean` |
| the paper's own Lemma 5, on `0 ≤ r ≤ 1` | one residual hypothesis | `BetaProdMGFBound` in `Lemma5PaperRange.lean` |

What the root actually proves is stronger than the `O(·)` sentence, in the one way that matters
here: the constant is explicit and `T`-free. `theorem2_rate` gives

```
|BR| ≤ 8·(C²/2 + 2C² + 2CD + C) · L · √(L³ · T · log T / η)
```

with `T = m·L`, so the whole numerical content of the paper's rate is machine-checked and the `L`
is kept visible rather than silently absorbed into a constant.

## Check it

One command does the whole verification:

```
cd lean4
./scripts/check_axioms.sh
```

It builds the root module, elaborates `TSDPP/Audit.lean` and rejects any elaboration error,
accounts for every `#print axioms` line by name, rejects any declaration depending on an axiom
outside the allowed three, scans every source file for `sorry`/`admit`/`native_decide`/`unsafe`/
`axiom`/`opaque` outside comments, and enforces that every module under `TSDPP/` is reachable from
the root. The same steps separately, plus the numeric falsifier, which the gate does not run:

```
export PATH="$HOME/.elan/bin:$PATH"
lake build                                    # the whole development
lake env lean TSDPP/Audit.lean                # the raw #print axioms report
python scripts/scan_forbidden.py              # the comment-aware source scan
python ../scripts/numeric_check.py            # the numeric falsifier, independent of the gate
```

Green means no `sorry`, no new axiom, no `native_decide`, no `unsafe`, and a clean `#print axioms`
on every audited declaration. It does **not** mean the statements are the ones the paper states:
that is a separate audit, [FIDELITY.md](FIDELITY.md), and its verdict is summarized under the
boundary of the artifact below. `Float` is the one item of the `CLAUDE.md` list that no gate
covers: `scan_forbidden.py` excludes it deliberately, so this item rests on review rather than on
a script.

## Where the paper does not go through

These are the places where the artifact could not follow the paper. Each states the paper's step,
what the artifact established in its place, and the scope of that finding. The full record is
[DESIGN.md](DESIGN.md) §5 and §7.

### 1. Lemma 5 is stated for `0 ≤ r ≤ 1` and applied at `r ≥ 1`

The paper states the Beta concentration inequality (p. 9, Eq (31)) for `0 ≤ r ≤ 1`, and Eq (33)
then applies it at `r = max{1, √(8 log T/α)}`, which is `≥ 1`. The artifact inherited the
out-of-range application, registered the `r ≥ 1` form with the constant `c₀ = 11/100`, and then
**refuted its own registered target inside Lean**: a `∀`-statement falls to one witness, and
`(α, β, r) = (1, 100, 14)` is a witness whose whole proof chain is a polynomial integral. The
certificate is the elementary containment `{X ≥ t} × {Y ≤ u} ⊆ {|X − Y| ≥ s}` whenever `s ≤ t − u`,
used at `t = 15/101`, `u = 1/101` where `t − u = 14/101 = s` exactly, so the lower bound is the
product of two `Beta(1, B)` one-sample tails, `LB = (86/101)^100·(1 − (100/101)^100)`. Against the
registered bound `2e^{−539/25}`, `LB / RHS = 75.79`.

The second headline theorem refutes the **paper's own constant `1/8`** on the same range, from the
same certificate. Both are unconditional and audited.

**Scope, which is the load-bearing part.** The paper's own Lemma 5, on `0 ≤ r ≤ 1`, is **not
refuted** — the witness sits at `r = 14`, entirely outside that range, and the range cannot be
violated at all: as `r → 0⁺` the ratio of the two sides tends to `1/2` from below. Neither is the
paper's theorem refuted. A proof step that does not go through does not make a theorem false, and
refuting the theorem would need a regret counterexample, which needs the problem statement this
artifact never formalized. What is established is that the bound the paper applies at `r ≥ 1` is
**false**, machine-checked and unconditional, and the consequence for the paper is a **citation
failure**: Eq (33) applies Lemma 5 outside the range it is stated for. `cards/L5-REFUTATION.md` §0 carries this scope note, and it
should be read before the number `75.79` is quoted.

The reason a constant this wrong survived to submission is structural, and it is the reason the
finding is worth the space: the true two-sample tail exponent is about `αr²/2` while the paper
claims `αr²/8`. On `r ≤ 1` the claimed exponent is far *larger* than the truth, so the bound is
comfortably satisfied and looks fine. The gap only opens at large `r`. A constant four times too
weak is invisible in exactly the regime the paper checks it in.

### 2. No range repairs the application

"Restate it on the range the paper printed" sounds like a paperwork fix and is not one, which was
worth establishing before investing in a repair. Three routes were tried and each dies for its own
reason. The union split needs `t₁ − t₂ = μ(1+δ₁−δ) ≤ rμ`, i.e. `r ≥ 1`, so the method's range and
the statement's range have disjoint interiors: at `r ≤ 1` the small-lower-tail choice `δ → 0`
forces `δ₁ ≤ r − 1 ≤ 0`, outside the admissible range `δ₁ > 0`. A one-sample Chernoff bound at
`r ≤ 1` has its threshold at or below the mean, where the optimiser degenerates and the bound
returns `1`; this is not a technicality, since the true probability at `r = 1` is `0.495857` at
`α = 1000, β = 100α`, essentially one half, against a target `e^{−α/8}` that is exponentially
small. And the exact two-sample union bound with exact Beta tails passes everywhere tested but
carries only about `2.2×` slack at its worst point, over a region whose supremum is `1/2`; the
integer-parameter case still needs a degree-`n` polynomial bounded uniformly in `(α, β)` by
`e^{−cαr²}`, which is a large-`n` asymptotic estimate and not a rewrite.

So there is **no range on which both the paper's application and the paper's bound are
simultaneously valid**. That is the finding, and it is what makes the refutation the deliverable
rather than a detour.

### 3. Eq (40)'s printed final step is false

Eq (40) is printed as a three-line chain. Verified at 600 dpi against the PDF's own character
stream, the last line has no parentheses around `1 − (16/η)e^{−η/8}`: the `1` is a bare additive
constant and only `(16/η)e^{−η/8}` carries the `1/T`. Read either way, the step is false rather
than merely unreconstructible. Its left side `Σ_{l≤n} L·2e^{−ηl/8}` is independent of `T` and
tends to `L·2e^{−η/8}/(1 − e^{−η/8})`, while its right side tends to `1`; at the paper's own
experimental setting (`L = 20`, `η = 2`) the left side is `140.83` and the right is `1.0062` at
`T = 10³`. The printed inequality asserts `140.83 ≤ 1`, falsified by one line of arithmetic that
[DESIGN.md](DESIGN.md) §3.1 records; `scripts/numeric_check.py` does not cover it.

The conclusion survives, and the reason is worth stating because it is what separates this from
the Lemma 5 finding: the excess is a **constant factor**, not a growth in `T`. With `L/η ≥ C + D`
from Corollary 1, the printed step asserts roughly `16(C+D) ≤ 1`; a constant-factor excess in the
tail is still `O(1)` in `T`, and after multiplication by `K = Θ(LC(C+D))` the ratio to the main
term tends to `0`. `TSDPP/Tail.lean` therefore proves the *true* bound, with the exponent constant
as a parameter `c > 0`, and `theorem2_withTail` keeps the tail as an abstract `B` with `0 ≤ B`
alone rather than committing to either expression; the upper bound `B ≤ √log T` enters only where
`B` is absorbed, in `theorem2_concrete` and `theorem2_rate`.

### 4. The `L³` exponent is not what the paper's own arithmetic yields

Theorem 2 and its abstract disagree: `O(√(L³T log T))` in §IV against `O(√(T log T))` in §I-C and
the conclusion. These agree only if `L` is treated as independent of `T`, and the paper never says
which it means. Carrying the paper's own arithmetic through with `L` symbolic gives
`BR(T) ≤ Θ(L)·2√(8T(C+D) log T)`, i.e. `O(L√(T log T))`, which is *stronger* than the claimed
`O(L^{3/2}√(T log T))`. So Theorem 2 is not falsified, it is implied; but the exponent it prints
is not the one its derivation yields, and neither is the abstract's. The artifact is agnostic
between the three readings: the assembly step is machine-checked as an exact finite-sum statement
with the exponent left symbolic, and `theorem2_rate` keeps the `L` visible rather than choosing a
convention for the paper.

### 5. `C` and `D` are not `T`-free constants

The paper bounds the copy age by `Y_i(t) ≤ C + D` inside the prefactor `(½C² + (2C² + 2CD + C)L)`
of Eq (38), and uses `(C+D)` there as a deterministic bound. The only source for the state bound is
Lemma 6, which is a *high-probability* statement with `D = ⌈log ε / log(1−θ_i)⌉`. Three
consequences the paper does not address: `D` depends on the confidence `ε` and hence on `T`;
`Y ≤ C + D` therefore holds only with probability `1 − ε`, so it cannot be pulled out of the
expectation as a constant factor without an extra tail term that Eq (38) does not carry; and `C`,
the maximum re-selection interval for a fixed arm, is itself what the policy controls, with no a
priori bound in the paper under the belief-DPP argmin. The gap is repairable by paying
`O(ε·L·maxY)`, and it is recorded rather than silently patched.

### 6. Eq (9)'s index convention is inconsistent with Eq (4)

Eq (4) defines `Y_i(t) = X_i(t−1) + 1` when `π_i(t) = 1`; Eq (9) writes the same quantity with
`X_{A_t}(t)`, one slot later. Both cannot be right for a deterministic `X`, and the difference is
exactly `1` in the slot where the event fires. The formalization pins Eq (4)'s convention, because
Eq (4) is the recursion that is actually defined. Eq (35) is invariant under the choice, since
both sides of the subtraction use the same index, so `penalty_diff` is unaffected either way; the
gap is bookkept rather than silently resolved because it *would* matter for any statement
comparing `X_i(t)` and `Y_i(t)` at the same slot, which Eq (36) does.

### 7. Lemma 3 and Lemma 4 are carried as hypotheses, not as axioms

The paper quotes both from [28] rather than deriving them. `CLAUDE.md` forbids introducing an axiom
to close a goal, so `TSDPP/Theorem2.lean` takes the decomposition and the per-round Bellman bound
as explicit premises `hdecomp` and `hper`, and proves everything that follows from them. A reader
who accepts [28] gets Eq (38) for free; a reader who does not can see exactly which step is being
assumed. The omitted intermediate is a probability space of trajectories with the policy-induced
measure, and Bellman operators on `L¹` of it; Mathlib has neither. Lemma 4 itself *is* proved in
its most general form (over an arbitrary measure space, in `TSDPP/Simulation.lean`), but it is not
wired in, because the trajectory law it would be instantiated against does not exist yet. That is
the largest open input in the development.

## The boundary of the artifact

`FIDELITY.md` audits the three ways a sorry-free development can still prove the wrong theorem:
too weak, vacuous, or shifted. It finds none of the three, and it names the boundary.

**The problem statement is not formalized.** All 13 numbered environments of the paper are
enumerated and dispositioned, but the equation-by-equation itemization in `FIDELITY.md` §1.0.1
marks the problem statement and the two definitions absent: Eq (5)–(7), the DPP index Eq (10), the
observation model Eq (11), the virtual queue Eq (12), the constrained policy Eq (13), the index
update Eq (14), the two likelihood factors Eq (20)–(21), the value function Eq (17) and the
Bayesian regret Eq (18). `BR` and `J` enter `theorem2_concrete` as abstract reals satisfying
hypotheses rather than as defined objects, and `cards/R4.md` records Eq (10), (12), (13) as
deliberately out of scope. Nothing is hidden, but the artifact formalizes the paper's *analysis*,
not its problem statement, so the precise claim it is entitled to is: *if* a policy admits the
regret decomposition and the concentration events the paper derives for its policy, *then* its
regret obeys the paper's rate. It is not entitled to claim that the paper's own constrained policy
attains that rate.

**The `O(·)` symbol itself is not formalized.** `theorem2_rate` is a machine-checked Lean theorem
of the form quoted above, with an explicit `T`-free constant. Passing to the `O(·)` *symbol* needs
a filter on `T` and a decision on whether `L` grows with it, which is the same convention question
as item 4. That is a modelling decision, not a mathematical gap, and the artifact refuses to make
it silently.

**The constant `c₀ = 11/100` is underived.** The route that would have justified it ran through a
ceiling for the union bound, and that ceiling claim was retracted: the displayed supremum was
mis-stated, and the finite-`α` consequences read off it do not follow. What survives is the
parameterisation. `TSDPP/Tail.lean` states the tail with the exponent constant as a parameter
`c > 0` rather than as `1/8` or `11/100`, so the paper's constant and the artifact's are two
instances of one statement. `K₀ = 100/11` enters through the concentration hypothesis `hdelta` and
through `eq39_collapse`, and is absorbed into `theorem2_rate`'s leading `8`; that theorem's own
radicand is `√(L³·(m·L)·logT/η)`. The rate is
unchanged either way, because the geometric series converges for every `c > 0`. This is the reason
the refutation does not depend on the retraction: the witness violates the paper's own `1/8` too,
by `353×` at the true probability.

**One route is proved but not formalized.** `cards/L5-CONVEX.md` carries a paper-level proof that
`Beta(a,b)` is dominated by `Γ(a, rate a+b)` in the convex order, which is a second and independent
route to Lemma 5 on the range where it is true. No node of it is in Lean. By this project's own
standard that card does not close Lemma 5, and it is reported here as owed rather than done.

## The experiments replica

[code/README.md](code/README.md) replays the paper's Section V experiments from scratch: the
synthetic setting, the Fig. 5 real-world trace, and the regret and estimation curves, with the
simulator, the CSVs every number is read from, and the figures. It is a separate deliverable with
its own record, and it documents eight differences from the paper, the first of which is
substantive: the paper's baseline ordering in Fig. 3 and Fig. 4 does not reproduce.
`src/diagnose.py whittle` points at the policy structure of the paper's oracle, and Difference 6
attributes part of the same effect to the episode-boundary flag chosen here.

## Issues

For bugs, questions, or discussions, please use the issues section of this repository.

## Contributions

We welcome contributions. Fork the repository, commit your changes, and make a pull request. Two
conventions are enforced by scripts and a change that breaks them will be visible: the bilingual
README pairs are checked by
[scripts/verify_translation_pairing.py](scripts/verify_translation_pairing.py), and the word
ceilings on the accretion-prone standing docs by
[scripts/verify_doc_budgets.py](scripts/verify_doc_budgets.py).
