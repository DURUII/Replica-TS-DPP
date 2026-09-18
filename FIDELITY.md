# FIDELITY — why the Lean statements are faithful to `<ROOT_STATEMENT>`

`CLAUDE.md` demands three separate things and forbids collapsing them:

1. a complete proof (or refutation) of `<ROOT_STATEMENT>` — in `DESIGN.md` §1–§7 and `cards/`;
2. a `sorry`-free Lean 4 formalization of it — in `lean4/TSDPP/`;
3. **a proof that the formalization is faithful to `<ROOT_STATEMENT>`** — this file.

Item 3 is not implied by items 1 and 2. A development can be sorry-free and still prove the wrong
theorem: too weak (an instance mistaken for the general claim), vacuous (hypotheses jointly
unsatisfiable), or shifted (a different quantifier order or inequality direction). This file audits
each of the three failure modes explicitly.

---

## 0. `<ROOT_STATEMENT>` and the shape of the claim

The paper's headline is **Theorem 2** (§IV, Eq (19)):

> `BR(T) = O( √(L³ · T · log T) )`,  where `T = m·L`.

`BR(T)` is itself defined by Eq (18) as `E[Σ_{t=1}^T r(t)] − E[Σ_{t=1}^T r*(t)]`. The claim is
therefore an **asymptotic, existential-constant** statement: there exist `T₀`, `c` with
`BR(T) ≤ c·√(L³T log T)` for all `T ≥ T₀`.

**The formalization does not prove this sentence verbatim.** It proves the stronger *concrete,
non-asymptotic, constant-explicit* bound `|BR| ≤ K·8·√(L³T log T/η)` as the Lean theorem
`TSDPP.theorem2_concrete`, in which the radicand `L³·T·log T` already appears. The bridge from
that to the `O(·)` sentence is §4 below, and it involves no new mathematics beyond bounding the
constant `K` by a multiple of `L`.

---

## 1. Does each Lean statement say what the paper says? (statement-by-statement)

For each item the three things that can silently drift are checked: the **direction** of the
inequality, the **quantifier order**, and the **domain** of the variables.

### 1.0 Coverage — every numbered item of the paper, and what happened to it

The fidelity question is not only "is each Lean statement faithful?" but "did anything get
silently dropped?".  This table enumerates *every* numbered environment in the paper (found by
scanning the PDF for `Definition n` / `Theorem n` / `Lemma n` / `Corollary n`) and states its
disposition.  Four dispositions are possible, and only the first two count as work done:

* **closed** — a `sorry`-free Lean declaration proves it as written;
* **closed, restated** — proved, but the statement had to be pinned down first (a gap or a
  divergence, itemized in §2–§3, never a weakening);
* **hypothesis** — carried as a *premise* of `theorem2_rate`/`theorem2_concrete`, never as an
  `axiom`.  The reader sees exactly what is taken on faith; `#print axioms` confirms these
  contribute nothing to the axiom footprint;
* **support only** — used by the proof chain, not a headline deliverable.

| paper item | disposition | Lean declaration |
|---|---|---|
| Definition 1 (AoI of event) | closed, restated | `TSDPP.chainPMF`, `chainPMF_sum_one`.  The *definition* itself — Eq (1), `X_i(t;θ) ≜ t − u_i(t;θ)` — is not a Lean definition; its content enters as the transition law of `chainPMF` |
| Definition 2 (event capture strategy) | support only | the selection variable `sel : Bool` of `TSDPP.copyStep`.  **The optimisation problem P1 and its constraints — Eq (5), (6), (7) — and the observation model Eq (11) are not formalized at all**; see §1.0.1 |
| Definition 3 (platform-copy AoI) | closed | `TSDPP.copyStep`, `copyStep_self`, `copyStep_other`, `copyStep_iterate` |
| Definition 4 (deterministic policy, [28]) | closed | `TSDPP.bestArm`, `bestArm_spec` (the argmin is attained) |
| **Theorem 1** (posterior update) | closed, restated | `TSDPP.betaPDFReal_conj`, `betaPDFReal_conj_all`, `lintegral_conj`.  What is closed is the **density-level** conjugacy; the index update Eq (14) and the likelihood Eq (20), (21) are not separately formalized — see §1.0.1 |
| **Theorem 2** (Bayesian regret bound) | **closed, restated** | `TSDPP.theorem2_rate`, `theorem2_concrete` (**ROOT**) |
| Lemma 1 (belief-DPP is a deterministic policy) | support only | `TSDPP.bestArm_congr` (the argmin is a function of the history) |
| Lemma 2 (Eq (23),(24) Lipschitz bounds) | closed | `TSDPP.l1_lipschitz`, `firstMoment_lipschitz` |
| Lemma 3 (regret decomposition, [28]) | **closed** | `TSDPP.sum_range_blocks`, `regret_decomp`, `episodeOf`, `regret_decomp_episodeOf` — the hypothesis `hdecomp` is derived, not assumed |
| Lemma 4 (per-episode decomposition, [28]) | **closed** | `TSDPP.simulation_lemma` (Eq (30)'s telescoping, on an arbitrary filtered probability space) and `TSDPP.bellman_step_le` (which derives `simulation_lemma`'s `hrec` from the two value recursions) — the hypothesis `hper` is derived, not assumed |
| Lemma 5 (concentration, [45]) | **NOT CLOSED — the registered form is FALSE** (traps P-64, P-67) | the union bound reduces it to `TSDPP.unionWitness` plus the Beta–Gamma ratio law, and that reduction is correct; but the artifact adopted `r ≥ 1` where the paper states `0 ≤ r ≤ 1`, and on `r ≥ 1` the bound fails exactly (`(2,200,10)` vs `11/100`; `(1,100,10)` vs `1/8`).  The paper's own range is true but unreachable by this method; see §3.4.  **P-67**: on Eq (33)'s own curve `r = max{1,√(8 log T/α)}` the **paper's** `1/8` fails too (5 of 6 sampled tuples, incl. `α=1, T=10⁶`), so the paper's *use* is false on its own settings |
| Lemma 6 (state bound `X_i(t) ≤ D`) | closed | `TSDPP.tail_le_eps` |
| Corollary 1 (`α^l_i ≥ η·l`) | **hypothesis** | premise `hηl` of `theorem2_rate`; **GAP-3**.  The premise captures *only* the inequality `α^l_i ≥ η·l`; the identification `η = ⌊L/(C+D)⌋` it is advertised as standing for is not formalized |

**Two rows above are qualified rather than plain `closed`.** Definition 1's list cited
`copyStep_iterate`, which is a statement about Definition 3, not Definition 1; and Theorem 1's
`lintegral_conj` closes the *density*, not the paper's Eq (14)/(20)/(21) index bookkeeping. Both
are coverage qualifications rather than divergences, which is why they are recorded here.

**One row is *under*-reported, in the artifact's favour.** `lintegral_conj` does more than the row
claims: it pins the normalising constant, turning the paper's Eq (22) proportionality
`∝ Beta(α+A, β+B)` into an **equality** of measures. That is a strengthening, and it is the reason
Theorem 1 is listed as *restated* rather than merely transcribed.

Two rows deserve emphasis because they are the ones a reader would most plausibly expect to be
missing and are not. **Theorem 1** is the paper's *other* named theorem, and it is closed:
`betaPDFReal_conj` is the Beta–Bernoulli conjugacy `Beta(α+A, β+B)` in its unnormalized density
form, `betaPDFReal_conj_all` drops the `0 < x < 1` side condition (both densities vanish outside),
and `lintegral_conj` pins the normalizing constant by integrating — it states that the
unnormalized posterior `x ↦ x^A(1−x)^B · betaPDFReal α β x` has total mass
`beta (α+A) (β+B) / beta α β`. That last one is the step that turns "posterior ∝ prior ×
likelihood" into an actual posterior. `cards/R7.md` records why this is in scope. **Definition 4 / Lemma 1** are closed as `bestArm_spec`
and `bestArm_congr`: the paper's Lemma 1 asserts the belief-DPP policy is a deterministic
function of the history, which is exactly the assertion that the argmin used by the policy is
attained (`bestArm_spec`) and depends only on its index argument (`bestArm_congr`).

**Two rows are not closed, and they are not the same kind of gap.**  Lemma 3 and Lemma 4 are
derived, not quoted — `regret_decomp_episodeOf` for Lemma 3,
and `simulation_lemma` + `bellman_step_le` for Lemma 4.  What remains is:

* **Lemma 5** (from [45]) — not a *hypothesis*, but **refuted in the form the artifact
  registered, and the gap is not a constant** (trap P-64, §3.4).  It is reduced to an
  elementary union bound with a fixed witness, that reduction is proved correct, and the
  *target* is **false** on the range the artifact adopted.  The paper's Lemma 5 is `0 ≤ r ≤ 1`; the
  artifact's is `r ≥ 1`; the artifact inverted the range, and on the inverted range the bound fails
  exactly (witnesses `(α,β,r) = (2,200,10)` against `11/100`, `(1,100,10)` against `1/8`).  What
  remains open is therefore **the paper's actual statement, on `0 ≤ r ≤ 1`** — which is true
  (`min c_eff = 0.242848` at the swept box's corner `(α,β,r) = (200,200000,1)`) and for which **no route is known**: the artifact's
  union-bound method *requires* `r ≥ 1` for its split, so it cannot be repointed at the true range.
* **The Corollary 1 premise `hηl`** — still a premise, and still the honest place to stop, because
  the identification `η = ⌊L/(C+D)⌋` depends on the episode bookkeeping the paper leaves informal.

What matters for fidelity is the *direction* of the dependency in both cases: `theorem2_rate` is
stated so that if a reader supplies the premise, the regret bound follows — the artifact never
assumes the conclusion it is trying to reach, and `#print axioms` confirms the premises contribute
nothing to the axiom footprint.  The difference between the two rows is that Lemma 5's gap is
*bounded and exhibited* (§3.4) whereas `hηl`'s is *unmodelled* (GAP-3).

### 1.0.1 Coverage of the 40 numbered equations

The table above enumerates the paper's *named environments*.  It does not enumerate the paper's
**40 numbered equations** (verified: the text contains tags (1)–(40) with none missing), and an
audit that claimed "nothing is silently dropped" on the strength of the environment table alone
would be over-claiming.  The equations are therefore itemised separately, with dispositions
**closed** (formalized), **implicit** (carried inside another declaration), **absent** (not
formalized):

| Eq | content | disposition |
|---|---|---|
| (1) | `X_i(t;θ) ≜ t − u_i(t;θ)`, AoI from the last update time | implicit — the transition law of `chainPMF` |
| (2), (3) | `Pr(X_i(t+1)=0) = θ_i`; `= X_i(t)+1` w.p. `1−θ_i` | closed — `chainPMF`, `chainPMF_sum_one` |
| (4) | `Y_i(t) = X_i(t−1)+1` if pulled, else `Y_i(t−1)+1` | closed — `copyStep`, `copyStep_iterate` |
| **(5), (6), (7)** | **the optimisation problem P1** — objective `min_π E[Σγ_i Y_i]`, the constraint `Σ_i π_i(t) = 1`, and the budget `Σ_t Σ_i π_i(t)c_i ≤ B` | **absent** — the artifact analyses the regret of a *given* policy; it never formalizes the constrained optimisation that selects one |
| (8) | a cross-reference ("Eq. (2) ∼ Eq. (4)"), not a formula | n/a |
| (9) | `r(t) = r(t−1) + 1 − γ_{A_t}(Y_{A_t}(t−1) − X_{A_t}(t))` | closed — `penalty_identity` (index convention pinned, GAP-5) |
| **(10)** | the DPP index (R4) | **absent** |
| **(11)** | `Ỹ_i(t) = π_i(t)X̂_i(t) + (1−π_i(t))(Y_i(t−1)+1)`, the *observed* AoI | **absent** — `copyStep` models the platform-copy AoI of Definition 3, not this observed quantity |
| **(12)** | the virtual queue `Z(t) = max{0, Z(t−1) + Σ_i π_i(t−1)c_i − B}` | **absent** |
| **(13)** | the constrained policy `π*(t) = argmin V Σγ_i Ỹ_i(t) + Z(t)(Σπ_i(t)c_i − B)` | **absent** — `bestArm` implements the *unconstrained* argmin of Definition 4 |
| **(14)** | the index update `α^{l+1}_i = α^l_i + Σ_j I_j`, `β^{l+1}_i = β^l_i + Σ_j s_ij − (1−I_j)s_ij−1` | **absent as an update rule**; only its *effect* is closed (Beta conjugacy, at density level) |
| (15), (16) | the belief law `P^θ_x` and its mean | closed — `Belief.pmf`, `pmf_sum_one`, `pmf_mean` |
| **(17)** | the value function `J_{π,t}(H) = E_{θ,π}[Σ_j r(j) | H]` | **absent** — `J` is never a defined object; `Theorem2` carries it as an abstract function |
| **(18)** | the Bayesian regret `BR(T) = E_{θ*∼Q}[E_{θ^l∼Q^l}[J^{θ^l}_{π^l,1}(∅)] − m·J^{θ*}_{π*,1}(∅)]` | **absent** — `BR` is an abstract real in `theorem2_concrete` |
| (19) | `BR(T) = O(√(L³T log T))` | closed as a concrete bound — `theorem2_concrete`; the `O(·)` symbol itself is `TSDPP.Asymptotic`, §4 |
| (20), (21) | the two-branch likelihood `Pr(s_ij | s_ij−1, n_j; θ_i)` | absent — subsumed by the density-level conjugacy |
| (22) | posterior `∝ Beta(α^{l+1}_i, β^{l+1}_i)` | closed **as an equality** — `betaPDFReal_conj`, `lintegral_conj` |
| (23), (24), (25), (26) | Lemma 2's Lipschitz bounds and their derivative | closed — `l1_lipschitz`, `firstMoment_lipschitz`, `armTerm_lipschitz` (trap P-10 for Eq (25)'s printing) |
| (27)–(34) | the regret decomposition and per-round bounds | closed — `regret_decomp_episodeOf`, `simulation_lemma`, `perRoundPenaltyDiff_le`, `stateTerm_le`, `regret_le` |
| (35) | Eq (9) after cancelling common terms | closed — `penalty_diff`, `bestArm_congr` |
| (36), (37) | the per-round penalty and state bounds | closed — `perRoundPenaltyDiff_le`, `stateTerm_le` |
| (38) | the finite-sum assembly | closed — `regret_le`, `eq39_collapse` |
| (39) | the collapse to `2L√(K₀m log T/η)`, `K₀ = 100/11` | closed — `eq39_collapse` (the paper prints `2L√(8m log T/η)`; the radius constant is `1/c₀`, see §3.4) |
| (40) | the geometric tail | closed, **restated** — `geom_exp_sum_le`, `tail_sum_le`; stated for a general exponent constant `c > 0` (`c = 1/8` is the paper's, `c = 11/100` what the chain consumes), and the paper's printed final step is false, see §3.1 |

**The gap this exposes, stated plainly.**  What the artifact formalizes is the **analysis chain**:
from a policy's regret decomposition (Eq (27)–(35)) through the concentration events (Eq (38)–(40))
to the rate (Eq (19)).  It does **not** formalize the **problem statement** — the constrained
optimisation P1 (Eq (5)–(7)), the virtual queue (Eq (12)), the constrained policy (Eq (13)), the
DPP index (Eq (10)), the observation model (Eq (11)) — nor the **definitions of the value function
and the Bayesian regret** (Eq (17), (18)).  Those objects appear in `theorem2_concrete` as abstract
reals (`BR`, `J`) and as hypotheses about them, rather than as definitions; `cards/R4.md` records
that Eq (10), (12), (13) are deliberately out of scope.

So the precise claim this artifact is entitled to is:

> *If* a policy admits the regret decomposition and the concentration events that the paper derives
> for its policy, *then* its regret obeys the paper's rate.

It is **not** entitled to claim that the paper's specific constrained policy — the one defined by
Eq (5)–(13) — attains that rate.  Closing that would require formalizing P1, the virtual queue and
the DPP index, which is a separate development.  This is recorded here rather than left for a
reader to discover, and it is the largest single limitation of the fidelity claim in this file.

### R1 / R2 — the model (Eq (2)–(4))

| paper | Lean | verdict |
|---|---|---|
| `X_i(t+1) = 0` w.p. `θ_i`, else `X_i(t)+1` | `chainPMF θ x y = if y=0 then θ else if y=x+1 then 1−θ else 0` | exact |
| "the above is a probability distribution" | `chainPMF_sum_one : Σ_{y<x+2} chainPMF θ x y = 1` | exact; **for every `θ`**, no side condition |
| `Y_i(t) = X_i(t−1)+1` if pulled, else `Y_i(t−1)+1` | `copyStep sel Xprev Yprev = if sel then Xprev+1 else Yprev+1` | exact |
| (implicit, used everywhere) `δ` slots on, the copy AoI is `λ+δ` | `copyStep_iterate : (copyStep false lam)^[δ] lam = lam + δ` | **recovers an unstated paper lemma**; this is what licenses the record `(λ,δ)` |

The paper never proves that the "record" `(λ_i, δ_i)` determines the law of `X_i(t)` — it is used
silently from Eq (15) onward. `copyStep_iterate` is what makes that legitimate, and it is stated
as its own theorem rather than folded into the `pmf` definition.

### R3 / R15 — the penalty (Eq (9), Eq (35))

Paper Eq (9): `r(t) = r(t−1) + 1 − γ_{A_t}(Y_{A_t}(t−1) − X_{A_t}(t))`.

Formalized as `penalty_identity`, which is the same identity rearranged and with the index
convention pinned (GAP-5). **Direction:** it is an *equality*, so no direction can drift — checked.
**Quantifiers:** `∀ N γ a X Y` with `Σγ = 1` as a hypothesis, matching the paper's standing
assumption `Σ_i γ_i = 1`, `γ_i ≥ 0`.

The step that deserves scrutiny is Eq (35), where the paper cancels the common terms between the
`θ*` and `θ` expectations. That cancellation is only valid if the *same arm* is pulled on the *same
history* under both parameters. The paper invokes Lemma 1 for this in one clause.
`Model.bestArm_congr` is that invocation made explicit; `penalty_diff` is the cancellation as a
theorem. **This is the single most load-bearing fidelity point in the development**: if the policy
were randomised, Eq (35) would be false, and `penalty_diff`'s statement would be too. It is not an
assumption smuggled into a definition — `bestArm` is a genuine function of the index vector.

### R5 / R6 — the belief law (Eq (15), Eq (16))

Paper Eq (15): `P^θ_x = θ(1−θ)^x` for `x < δ`, `P^θ_{λ+δ} = (1−θ)^δ`.
`Belief.pmf` is this, verbatim, including the two-branch structure.

| check | result |
|---|---|
| is it a distribution? | `pmf_sum_one : Σ_{x<λ+δ+1} pmf θ λ δ x = 1`, **for every `θ`** |
| is Eq (16) the mean? | `pmf_mean : Σ_x x·pmf θ λ δ x = (1−θ)/θ + (1−θ)^δ(λ − (1−θ)/θ)` |

**Domain caveat, stated rather than hidden:** `pmf_mean` requires `θ ≠ 0`. The paper's Eq (16)
divides by `θ` too, so this is the paper's own restriction, not a weakening introduced here. The
`θ = 0` case is not merely unproved — it is *degenerate* (the chain never resets, so the mean is
`+∞`, not a real number). By contrast `pmf_sum_one` and both Lipschitz bounds are **unconditional
in `θ`**, so nothing downstream inherits the restriction (trap P-2).

### R9 — Lemma 2 (Eq (23), (24))

Paper: `Σ_x |P^θ_x − P^θ'_x| ≤ 2δ|θ−θ'|` and `Σ_x x|P^θ_x − P^θ'_x| ≤ (δ(δ−1)/2 + δ(λ+δ))|θ−θ'|`.

Both are formalized as `l1_lipschitz` and `firstMoment_lipschitz` with the **same constants** and
the **same `≤` direction**, over `θ, θ' ∈ [0,1]` closed (the paper's interval; the endpoint is
handled explicitly, trap P-3).

**These constants are tight and the development knows it.** `scripts/numeric_check.py` maximises
`|LHS|/|θ−θ'|` and returns `1.0000000000000113` for Eq (23) and `1.0000000000000226` for Eq (24).
A formalization that silently *loosened* either constant would pass `lake build` and still be
faithful in direction — which is why tightness is checked numerically and recorded. Conversely, a
downstream step that *needs* the tight constant (Eq (38) does) would be broken by a loosening, so
the numeric check is doing real work here, not decoration.

**A correction, not a weakening (trap P-10):** the paper prints `f'(ξ) = (1−ξ)^{x−1}(1−(x+1)ξ)`
for Eq (25). Under Lean's truncated `ℕ`-subtraction this is wrong at `x = 0` — `(1−ξ)^{0−1}`
evaluates to `1`, not `(1−ξ)^{−1}`. The formalization uses the un-truncated form
`(1−θ)^x − θ·x·(1−θ)^{x−1}`, which is the correct derivative at every `x`. This is a case where
the *formalization* is right and the *paper's printed formula* is right only for `x ≥ 1`; the
bound `sup|f'| ≤ 1` — which is what Eq (25) is actually used for — holds in both readings.

### R10 / R12a — Lemma 6 and the state bound

Paper Lemma 6: `Pr(X_i(t) ≥ d) ≤ ε` for `d = ⌈log ε / log(1−θ_i)⌉`.
Formalized as `StateBound.tail_le_eps : (1−θ)^⌈log ε / log(1−θ)⌉₊ ≤ ε`, fed by
`Model.chain_path_no_reset : ∏_{x<d} chainPMF θ x (x+1) = (1−θ)^d`.

The product-vs-`Pr` step is where the two correspond: the event "never resets in `d` slots" is the
*single* trajectory `0→1→…→d`, so its probability is the product of the `d` upper-branch
transition probabilities. `chain_path_no_reset` is exactly that product. No measure space is
needed and none is constructed — which is a fidelity-relevant *simplification*, not a gap, because
the product is literally the probability of that one path.

**The formalization is strictly stronger than the paper here:** the paper says "for any `ε > 0`"
and then reasons with `ε ∈ (0,1)`. The formalization carries no `ε < 1` hypothesis: the linter
reports it unused, and dropping it is the correct repair rather than silencing the warning. For
`ε ≥ 1` the bound is trivial, so the theorem covers it.

### R13 / R14 — the tail and the finite-sum assembly (Eq (39), (40))

`Assembly.sum_range_inv_sqrt_le` is the source of the paper's `2√m`:
`Σ_{l<m} 1/√(l+1) ≤ 2√m`. Numerically sharp (`0.988516` of the bound attained), so no slack was
introduced. `Tail.geom_exp_sum_le` / `tail_sum_le` formalize the geometric tail, stated for a
general exponent constant `c > 0` (`c·η` in place of the paper's `η/8`). The radius constant
`K₀ = 1/c₀` that the substitution forces on Eq (33) is what makes the collapsed divergence
`2L√(K₀m log T/η)` rather than the paper's `2L√(8m log T/η)` — see §3.4.

**This is where the formalization deliberately departs from the paper's printed text** — see §3.

> **[CORRECTED — trap P-64.]**  The superseded reading held that "the paper's `c = 1/8` and the
> artifact's `c = 11/100` are then the same theorem rather than two statements, so the divergence
> recorded in §3.4 enters as a *substitution* at the use site."
>
> That is the correct description of what `Tail.lean` *proves* — `c` really is a free parameter, and
> the `11/100 → 1/8` rewrite really is a substitution there. What is withdrawn is the implication
> that the substitution is *harmless*. It is not, because the two constants are attached to
> different ranges (P-64): `1/8` is the paper's constant on `0 ≤ r ≤ 1`, and `11/100` is the
> artifact's on `r ≥ 1`, where the bound is **false**. So this is not a constant substitution
> between two statements of one theorem; it is a substitution between a statement that holds and one
> that does not. The algebraic content of `Tail.lean` and of `Rate.rate_core` is unaffected — the
> `K₀ = 100/11` chain is internally valid — but the *provenance* of `c₀ = 11/100` is now
> **[UNDERIVED]** (P-62 layer 3's ceiling argument is retracted), so `K₀` is a free parameter that no
> surviving argument pins. Whether that matters downstream is a separate question from whether the
> chain is correct; both are recorded rather than merged.

### R16 / R17 — Theorem 2

`Rate.rate_core` proves the final arithmetic `2L√(K₀Z) + B ≤ 8√(L⁴Z)` with `K₀ = 100/11` and
`Z = m·log T/η` (the paper's `2L√(8Z) + B ≤ 7√(L⁴Z)` at its radius `√8`), and
`Theorem2.theorem2_concrete` assembles the whole chain into
`|BR| ≤ K·8·√(L³·(m·L)·log T/η)`.

| check | result |
|---|---|
| direction | `≤` throughout, as in the paper |
| is `L³T log T` present? | yes — as `L³·(m·L)·log T`, i.e. `L³T log T` under `T = mL` |
| is the constant explicit? | yes — `8`; near-tight, since the explicit witness `L = m = logT = η = 1`, `B = √log T` gives `2√(100/11)+1 = 7.0303`, and `7` — valid at the paper's `2√8+1 = 6.657` — is refuted by it (trap P-19) |
| is the tail hidden? | no — `B` is an explicit parameter with `0 ≤ B` and `B ≤ √log T` as hypotheses |
| numerical falsification | 0 violations over a grid at the `hηT`/`hBle` boundaries; `eq39_collapse` attains `0.889` of its bound |

The one thing *not* machine-checked is the passage to `O(·)` — see §4.

### Quantifier-order spot check on the headline

The paper's Theorem 2 is `∃c, ∃T₀, ∀T ≥ T₀ : BR(T) ≤ c√(L³T log T)`.  `theorem2_concrete` states
`∀(all parameters) → hypotheses → |BR| ≤ K·8·√(…)`.  The Lean statement has **more** universal
quantifiers (every parameter is universally quantified, not existentially chosen) and **no**
`T ≥ T₀` restriction.  A statement with more `∀`s and a weaker hypothesis is *stronger*, so this
direction of drift is the safe one — but it is checked explicitly here because a formalization
that had accidentally *exchanged* the quantifiers (e.g. `∃K, ∀m`) would be a genuine fidelity
failure and would look almost identical in the source.

---

## 2. Is anything vacuous? (the satisfiability audit)

A statement with jointly unsatisfiable hypotheses is `sorry`-free and worthless. Each theorem with
non-trivial hypotheses was checked to have a witness:

| declaration | hypotheses | witness | non-vacuous |
|---|---|---|---|
| `l1_lipschitz` | `θ,θ' ∈ [0,1]` | `θ = 0`, `θ' = 1` | ✓ (bound is tight there) |
| `firstMoment_lipschitz` | `θ,θ' ∈ [0,1]` | `θ = 0`, `θ' = 1` | ✓ |
| `perRoundPenaltyDiff_le` | `N`; `γ ≥ 0`, `Σγ = 1`; `δ ≤ C`; `λ+δ ≤ L`; `θ,θ' ∈ [0,1]` | `N=2`, `γ=(½,½)`, `λ=δ=C=1`, `L=2`, `θ=0`, `θ'=1` | ✓ |
| `stateTerm_le` | `δ ≤ C`; `∀x, |J x| ≤ (C+D)L`; `θ,θ' ∈ [0,1]` | `J ≡ 0` (and `J ≡ (C+D)L`) | ✓ |
| `episodeRegret_le` | `regret = Σ_t diff t`; `∀t, |diff t| ≤ K·delta t` | `diff ≡ 0`, `delta ≡ 0` | ✓ |
| `regret_le` | `∀l, |episodeRegret l| ≤ K Σ_t delta l t` | `episodeRegret ≡ 0` | ✓ |
| `tail_le_eps` | `0 < θ < 1`, `0 < ε` | `θ = ½`, `ε = 1` (then `ε ≥ 1`, covered) | ✓ |
| `geom_exp_sum_le` | `0 < η`, `0 < c` | `η = c = 1` (also `η = 1, c = 11/100`) | ✓ |
| `sum_inv_sqrt_weighted` | `C ≥ 0`, `η > 0`, `∀l, η(l+1) ≤ ηl l` | `η = 1`, `ηl l = l+1` | ✓ |

Note the last row: `ηl l = l+1` is exactly the shape Corollary 1 supplies
(`α^l_i ≥ η·l`), so the hypothesis is not an artefact of the proof — it is the paper's own
intermediate result.

Of the three citation nodes, **two are not hypotheses**: `L34` (Lemma 3+4 of [28]) is
**derived** — `regret_decomp_episodeOf`, `simulation_lemma`, `bellman_step_le` — and `L5` (Lemma 5
of [45]) is reduced to an elementary union bound with a fixed witness (§3.4). Only `L5`'s
constant and the Corollary 1 premise `hηl` remain unreached, and both are *visible in the
statement*.

This distinction matters for fidelity: an `axiom` would make the surrounding theorem true by fiat
and hide what is assumed; a hypothesis makes the dependence visible to a reader. A reader who does
not accept [28] can check the derivation instead of taking it on faith, and a reader who wants
the paper's exact `1/8` is told exactly which lemma to prove (§3.4). `#print axioms` on every
declaration listed above returns `[propext, Classical.choice, Quot.sound]` — the surviving premises
contribute **nothing** to the axiom footprint.

---

## 3. Where the formalization is *deliberately different* — and why that is fidelity, not drift

Three places the Lean statements do **not** transcribe the paper's printed text. In each case the
divergence was forced, is documented, and does not weaken the conclusion.

### 3.1 Eq (40)'s constant (GAP-6)

The paper prints the tail bound as `(1 − (16/η)e^{−η/8})·(1/T) + 2m/T`. This is not
reconstructible: `Σ_{l≥1} 2e^{−ηl/8} = 2e^{−η/8}/(1−e^{−η/8}) ≈ 16/η`, so the derivation supports
`≈ 16L/η`, not `O(1/T)`; and `2m/T = 2/L` differs from the derivable `2` by a factor `L`.

`Tail.lean` proves the **honest** bound, not the printed one. The justification for calling this
faithful rather than divergent: the printed constant is `O(1)` in both readings, it is multiplied
by the `O(L)` coefficient in Eq (38), and it is asymptotically dominated by the leading
`Θ(√(L³T log T))` term for `T ≥ 2`. So **the printed defect cannot change Theorem 2's exponent** —
which is the only thing Eq (40) is used for. If the tail term had been of the same order as the
leading term, this would have been a genuine fidelity failure; it is not, and the arithmetic is
recorded in `DESIGN.md` §7 GAP-6 and `cards/R13.md`.

### 3.2 Eq (9)'s index convention (GAP-5)

Eq (4) refreshes from `X_i(t−1)`; Eq (9) prints `X_{A_t}(t)`. They differ by one slot and cannot
both hold for deterministic `X`. The formalization pins Eq (4)'s convention. Justification:
Eq (35) — the only place Eq (9) is consumed — is a *difference* of two expectations that both use
the same convention, so the off-by-one cancels. `penalty_diff` is unaffected either way, and this
was verified by re-deriving rather than asserted.

### 3.3 `L` vs `C+D` in Eq (36) (rejected route J-9)

The paper's Eq (38) expands to `(½C² + LC) + 2C(C+D)L`. Lemma 6's route (`λ+δ ≤ C+D`) gives
`C(C+D)` in place of `LC`, leaving `2C²L` unmatched. `perRoundPenaltyDiff_le` uses `LC`, valid
because inside an episode of length `L` the copy-AoI satisfies `λ+δ ≤ L` trivially. Sympy confirms
the printed expansion matches `LC` and not `C(C+D)` (difference exactly `0` versus nonzero), so
`LC` is not a convenient choice — it is the one the paper's own printed constant requires.

---

### 3.4 Lemma 5's constant: `11/100` replaces `1/8` (GAP-2)

> **[SUPERSEDED IN PART — trap P-64.]** This section is written on the premise that the
> artifact and the paper differ **only in a constant**. They do not: they differ in the **range** of
> `r`. The paper's Lemma 5 is `0 ≤ r ≤ 1`; the artifact's target is `r ≥ 1`. The artifact therefore
> did not weaken a true statement, it **inverted the range of a true statement into a false one** —
> exact counterexample `(α,β,r) = (2,200,10)`, and the paper's own constant `1/8` fails too, at
> `(1,100,10)`. The `[UNDERIVED]` marker on `11/100` (below) stands and is now doubly justified: not
> only did P-62 retract the argument that produced it, P-64 shows the constant it names is attached
> to a false statement. **The `0.123302` ceiling is *not* among what stands** — it is the headline of
> P-62's retracted layer 2 (`sup_ρ min_δ max = 0.8839970429` is a limit, not a lower bound at finite
> `ρ`), so the sentence below that presents it as "the ceiling of the method, computed in closed
> form" is a **rejected route**, retained only as a record. What falls is not merely the framing that
> the *only* question was which constant; it is also the *ceiling* that framed it. See `DESIGN.md`
> P-62 and P-64, and J-11 for the route analysis that replaced them.

This is the one place where the artifact's **statement** differs from the paper's, so it needs the
most care — but per the P-64 banner above it is not accurate to call the difference a
"numerically weaker" version of the same claim. The claim as written was:

> **`1/8` is unreachable by the union-bound method, and `11/100` is what that method provably
> yields.** The ceiling of the method is `0.123302`, computed in closed form.

**[RETRACTED — traps P-62 (layer 2) and P-64.]** Both halves fail. The ceiling is not a
ceiling (layer 2's `0.8839970429` is `sup_ρ min_δ max`, approached from below, so `min_δ max` is
*below* it at every finite `ρ`), and `11/100` is not "what the method yields" in any region where
the method is informative (P-64: outside the vacuous region `ρ ≤ r−1` the antecedent is
unsatisfiable on `r ≥ 1`). What survives from this section is the *algebra of the substitution* —
that the geometric tail is stated at a free `c > 0` and the paper's final constant is coupled to it
— not any claim that `11/100` is the constant the method reaches.

*(Scope, per P-64: this is a statement about the method's reach, not about the truth of either
constant. `11/100` being "what the method yields" is compatible with `11/100` being **false as a
bound** on `r ≥ 1` — and it is. The two are different objects; see the two-fidelity-rules table in
`DESIGN.md` §6.)*

**Why this is a fidelity defect and not a fidelity failure.** The paper's Lemma 5 is invoked in
exactly one place — Eq (33)→(40) — and in exactly one way: to bound `Pr(ε^c_i) ≤ 2e^{−α^l_i r²/8}`,
after which Eq (40) sums a *geometric series* `Σ_l 2L·e^{−c α^l}` with `α^l ≥ ηl`. A geometric
series converges for **every** `c > 0`. Changing `1/8` to `11/100` therefore:

* changes the *constant* in the exponent, and hence the constant multiplying the final bound;
* does **not** change the rate — `O(√(L³T log T))` is identical, and `TSDPP.bound_isBigO_sqrt_log`
  is insensitive to `c`;
* does **not** change any step's *form*, quantifier order, or the set of hypotheses.

So the artifact's Theorem 2 is the paper's Theorem 2 up to the constant inside an exponential that
the paper's own final `O(·)` discards. §4 states this bridge explicitly, which is why the weakened
constant does not propagate.

**Why the gap is exhibited rather than merely admitted.** `DESIGN.md` GAP-2b records the closed-form
ceiling `sup_{s,ρ}[A(s)^α+B(s)^α]^{1/α} = 0.883997` at `t = 1/(e−1)`, giving `c = 0.123302 < 1/8`.
The supremum is attained only as `ρ → ∞`, which is why it is invisible to any finite grid — a trap
logged separately (P-23).

**[CORRECTED — trap P-62.  The displayed supremum above is mis-stated; no replacement bound on `r` or `α` is asserted here.]**
`sup_{s,ρ}[A(s)^α+B(s)^α]^{1/α} ≥ 1`,
not `0.883997`: the `sup` ranges over `s → 0` (equivalently `δ = ρs → 0`), where `A → 1` and
`B → 0`, so `[A^α+B^α]^{1/α} → max(A,B) → 1`, and a quantity that is `≥ 1` cannot equal `0.883997`.
What GAP-2b's calculation (the crude bounds `A ≤ (1+t)e^{−t}`, `B ≤ te^{1−t}`, minimised at
`t* = 1/(e−1)`) actually establishes is
`sup_ρ min_δ max(A,B) = e/(e−1)·e^{−1/(e−1)} = 0.8839970429`, i.e. `−log = 0.123302` — a statement
about the `ρ → ∞` limit of `min_δ max(A_ρ,B_ρ)`, not an identity for `[A^α+B^α]^{1/α}` at fixed `α`
(which is why the finite grid could not see it — P-23).

Two *finite-`α`* consequences of the union bound are **not** asserted — a `ρ`-uniform ceiling on **`r`**
(`r ≤ 1.058737`), then a `ρ`-dependent one (`r ≤ sqrt(−log m(ρ)/(11/100))`: `2.1435` at `ρ = 1/2`,
`1.6172` at `ρ = 1`, `1.3467` at `ρ = 2`, `1.1773` at `ρ = 5`, `1.0889` at `ρ = 20`, `1.0648` at
`ρ = 100`, `1.0587` only as `ρ → ∞`).  Both are **[RETRACTED — 该替换使用了对称切片的一维下界,对
`hnum` 无效]**: `hnum` binds **two independent parameters** (`δ₁` inside `chernoffA`, `δ` inside
`chernoffB`) linked only by `hrel : δ₁ ≤ r−1+δ`, so the symmetric slice `δ₁ = δ` (with `B` monotone,
valid only at `r = 1`) gives a `1`-D infimum that is an **upper** bound of the `2`-D infimum over the
admissible set, not a lower bound; and that `2`-D infimum **collapses to `0`** whenever `ρ ≲ r−1`
(take `δ₁ → ρ⁻` so `A(δ₁) → 0`, and `δ → 0` so `B(δ) → 0`).  `hnum` is therefore satisfiable for
arbitrarily large `r`: **this route yields no upper bound on `r` at all**, and no positive bound is
asserted here.  The three-layer record is `DESIGN.md` trap P-62.

**Two guards (trap `P-63`), which qualify that sentence in both directions.**  **(i)** The collapse
set *is* the vacuous set: with `s := r/(1+ρ)` the event level, `Pr(|X−Y| ≥ s)` is *null* exactly when
`r ≥ 1+ρ`, i.e. `ρ ≤ r−1` — the identical inequality.  Every witness of the collapse is a witness on
which the target has no content, so the collapse is not evidence that the method is *strong* at large
`r`.  (Precisely the criterion is `μ E = 0`, not `E = ∅`: on the boundary the event
`{|X−Y| ≥ 1}` is `{(0,1),(1,0)}` — non-empty but null for `α, β > 0`.)
**(ii)** For a **fixed** cap `s ≤ s₀ < 1` there *is* a ceiling, diverging as `s₀ → 1`:
`r*(s₀) = 6.159`, `8.554`, `12.138`, `20.460`, `40.187`, `61.073` at `s₀ = 0.3`, `0.5`, `0.7`, `0.9`,
`0.99`, `0.999` — the largest root of `G(r,s₀) = 0.11 r²`, `G(r,s) = −log A(r−1)`
(`= −log r − ((r−s)/s)·log(r(1−s)/(r−s))`); `α → ∞` indicators, not theorems.  The honest
form: **no absolute ceiling; the ceiling is bought entirely with vacuity** — by `ρ ↓ r−1`, i.e. by the
tail event approaching a null set, not by the paper's `r ≥ 1`.  **(iii)** Also retracted: "on `ρ > r−1`
the constrained infimum *is* `m(ρ)`".  The constraint is slack, so `A` may be evaluated at `r−1+δ`: at
`ρ = 10`, `r = 1.1` (event level `0.1`, far from vacuous) the admissible pair `δ₁ = 0.6`, `δ = 0.5`
gives `max = 0.861784` and the true constrained infimum is `0.846523`, both below `m(10) = 0.871389`.
`m(ρ)` bounds the constrained infimum from neither side.

**`11/100` itself is `[UNDERIVED — 常数依据待独立重导]`**: the `α ≈ 52` threshold it was originally
read off is downstream of the false chain, and no replacement derivation is claimed here.
This is *not* a claim of a sealed wall at `r ≈ 1.06`.
The claim that "GAP-2c records the two routes that *would*
reach `1/8` and why each is out of scope" presupposes the union-bound route *cannot* reach
`1/8`, which rests on `−log m(ρ) ≤ 0.123302` being an upper bound on the achievable exponent — and it
is not: the constrained infimum collapses (guard (i)), so the achievable exponent is unbounded above
(`r = 2`: `0.4685` at `s = 0.9` rising to `4.4319` at `s = 1−10⁻⁸`; `r = 5`: `0.3191` → `2.8472`).
So `1/8` is **not** excluded by this method; it is merely not reached here.  GAP-2c's *positive*
content — that the `2`-D Chernoff route needs `₁F₁` (absent from Mathlib, no short path) and the exact
conditioning needs a uniform Laplace-type lower bound on `B(α,β)` — is untouched by this correction and
still tells a reader who wants `1/8` which lemma to prove.

**Why the constant is `11/100` and not something closer to a limit.** The witness is `t = 29/50`, and
every step must be discharged by rational arithmetic. `11/100` leaves provable margins of 1.26%,
1.48% and 11% on the three comparisons; pushing closer to whatever the method's true reach is would
leave margins under 1% and make the Lean proof depend on the last digits of an `exp` bound. The
concession buys a robust proof. It is a *deliberate* trade, recorded so that no future reader
mistakes it for an overshoot.

The concession is not read off any ceiling: there is no established ceiling to push toward
(P-62 layer 2 retracts `0.123302` as a bound), so the choice is not justified by proximity to one. The *arithmetic* reason above is
unaffected and is the reason that survives: what is being bought is margin under a rational
witness, not a fraction of a known limit. Note also that `11/100` is not merely "conservative" —
P-64 shows it is **false** on the registered range, so the number this paragraph explains is the
number the artifact uses, not a number that has been shown admissible anywhere.

**Notation, so the three documents can be read side by side.** This section writes the split point
as `t`; `cards/L5.md` writes the same quantity as `δ = ρs`, where `s` is the witness and `ρ = β/α`.
This section's `L` is `cards/L5.md`'s `B`. They agree: in regime 1 the witness forces `δ = ρs =
29/50` *identically*, which is exactly this section's `t = 29/50`. Re-derived independently at
40 dps — `sup_ρ min_δ max(A,L)` is **monotone increasing in `ρ`** (checked at 14 values from
`ρ = 1` to `ρ = 10⁶`, no decrease) and converges to the closed form `0.883997042903`, i.e.
`−log = 0.12330156 < 1/8 = 0.125`, which is the claim.

**And a value that looks like a contradiction but is not.** The witness bound
`sup_ρ max(A,B) = 0.884639270` *exceeds* the ceiling `0.8839970429`. That is required, not an
error: the ceiling is the supremum over `ρ` of the value at the *optimal* `δ* = 1/(e−1) =
0.5819767`, whereas the witness is the fixed rational `δ = 29/50 = 0.58 < δ*`. Since
`A(δ) = (1+δ)e^{−δ}` is decreasing on `δ > 0`, a rational just *left* of `δ*` must give a larger
value. The ceiling is what an optimiser would reach; `29/50` is what the Lean can discharge by
rational arithmetic. Both are `≤ e^{−11/100} = 0.895834135`, with the witness leaving a 1.25%
margin.

**Paper's own inconsistency — and it is a live defect, not a reconcilable one.** Lemma 5 is stated
"for all `0 ≤ r ≤ 1`", but Eq (33) uses `r^l_i = max{1, √(8 log T/α^l_i)} ≥ 1` and cites the lemma at
that `r`.  The argument that the two are "reconcilable" —
`{|X−Y| ≥ rμ} ⊆ {|X−Y| ≥ μ}` for `r ≥ 1`, "so only the `r = 1` case is ever needed, which is what
the artifact proves" — is **invalid**.

The containment is real but irrelevant: it compares the *events*, while the bound's right-hand side
`2e^{−αr²/8}` shrinks with `r` at the same time.  The claim is *harder* at large `r`, not easier — at
`r = 1` the right-hand side is `2e^{−α/8} ≥ 1` for every `α ≤ 8 log 2 = 5.545`, so that case is
vacuous, whereas at `r = 10` the right-hand side is `2e^{−25α/2}` and the probability must match it.
Passing from the event `{|X−Y| ≥ rμ}` to `{|X−Y| ≥ μ}` therefore buys nothing: it replaces the
statement by a *different, unproved* one whose right-hand side no longer matches.

And the `r ≥ 1` claim is not merely unproved, it is **false**.  Exact rational arithmetic (each row
reproduced independently at 40 dps — see `DESIGN.md` P-64 for the table and the method):

| `(α, β, r)` | `Pr(\|X−Y\| ≥ rα/(α+β))` exact | vs `11/100` | vs the paper's `1/8` |
|---|---|---|---|
| (1, 100, 10) | 2.809651246898e−05 | holds | **fails 3.77×** |
| (2, 200, 10) | 8.606640056681e−09 | **fails 15.43×** | fails 311× |
| (5, 500, 10) | 3.658586854855e−19 | **fails 1.4e5×** | fails 2.6e8× |

So the artifact did **not** inherit a harmless inconsistency: it inherited the paper's out-of-range
application and then *formalized that application*.  The honest statement of the position is:

* the paper's Lemma 5, **as printed** (`0 ≤ r ≤ 1`, `c = 1/8`), is **true** — a sweep of
  `α ∈ [0.5, 200]`, `ρ ∈ [0.1, 1000]`, `r ∈ [0.1, 1]` gives `min c_eff = 0.242848` at the corner `(200,200000,1)`, clearing `1/8` by
  +0.113;
* the paper's **application** of it at `r = max{1, √(8 log T/α)}` is **false** from `T ≈ 10⁵`
  (`(α,β) = (1,100)`, `T = 10⁶` ⟹ `r = 10.513`, `c_eff = 0.10623 < 1/8`);
* the artifact's registered target — the application, at `c = 11/100` and `r ≥ 1` — is **false**.

The artifact's own union-bound split is what made `r ≥ 1` look natural: taking `t₁ = μ(1+δ₁)`,
`t₂ = μδ` gives a gap `μ(1+δ₁−δ)`, so small tails (`δ, δ₁ → 0`) *require* `r ≥ 1`.  At `(2,200,10)`
the best admissible split, `δ₁ = r−1 = 9`, `δ → 0`, yields `A^α + B^α = 6.431e−7` against the
required `2.789e−10` — a 2305× miss.  The method's hypothesis and the statement's truth have
disjoint interiors; see `DESIGN.md` P-64(c).

#### 3.4.1 The paper's `8` is *coupled*, and decoupling it forces the radius constant `K₀ = 100/11`

`c₀ = 11/100` is a weaker exponent than the paper's `1/8`, but it does **not** simply weaken the
final bound: the paper's `8` occurs in three places and two of them are load-bearing in different
ways, so replacing `1/8` by `11/100` has to be propagated deliberately. The three occurrences:

1. Eq (33) sets the confidence radius `r^l_i = √(8 log T/α^l_i)`, chosen so that `α r²/8 = log T`
   and the per-episode failure probability is `2e^{−log T} = 2/T`.
2. Eq (40)'s tail uses `2e^{−α^l/8}`, which comes from `r^l ≥ 1 ⟹ (r^l)² ≥ 1` — so the *tail*
   exponent carries `r² = 1` and **not** the `8` of the radius. These two are easy to conflate.
3. The truncation index `n = ⌈8 log T/η⌉` and the additive `2m/T` slack are the same fact read twice.

**Consequence, and the reason `K₀ = 100/11` and not `8`.** The tail's geometric ratio is
`e^{−c₀η}` for *any* choice `K` of radius constant — occurrence 2 above is what makes that true.
`K` therefore controls only the `2m/T` term, via the identity `α r²/8 = log T` of occurrence 1:
to keep the failure probability at `2e^{−log T}` with exponent `c₀` instead of `1/8`, one needs
`c₀·K = 1`. So `K₀ = 1/c₀ = 100/11` — that is *all* `100/11` is, the reciprocal of `11/100`.
Everything downstream that mentions the radius follows mechanically:

| site | paper (at `c = 1/8`, `K = 8`) | artifact (at `c₀ = 11/100`, `K₀ = 100/11`) |
|---|---|---|
| `Tail.geom_exp_sum_le` / `tail_sum_le` | ratio `e^{−η/8}` | ratio `e^{−c₀η}`, `c` a parameter |
| `Eq39.eq39_collapse` | `L·2√(8m log T/η)` | `L·2√(K₀m log T/η)` |
| `Rate.rate_core` | `2L√(8Z) + B ≤ 7√(L⁴Z)` | `2L√(K₀Z) + B ≤ 8√(L⁴Z)` |
| `Theorem2.theorem2_concrete` / `theorem2_rate` / `theorem3_rate` | constant `7` | constant `8` |

**The final constant moves `7 → 8` for a reason that is invisible in the first summand.** The
intermediate bound is `2√(K₀Z) ≤ 7√Z` and it *survives*: `2√(100/11) = 6.030227 ≤ 7` with `0.97` of
slack, and the proof step needs only `100/11 ≤ 49/4 = 12.25`. It is the tail's `+1` that crosses:
`2√(100/11) + 1 = 7.030226`, so the constant `7 = 6 + 1` (valid at the paper's `2√8 + 1 = 6.656854`)
becomes `8 = 7 + 1`. Both numbers are checked, and the check that matters is the *second* one —
this is trap P-19 re-armed (see P-19 and P-48).

**What `K = 8` would cost, recorded rather than silently avoided.** Keeping the paper's radius
constant would give a tail term `2m/T^{0.88} = O(T^{0.12}/L)`. That does **not** destroy the rate —
it is dominated by the main term, since `T^{0.12}/(L^{1.5}T^{0.5}√log T) → 0` — but it is no longer
`O(1/L)`, so the final bound would need a `T`-dependent constant or a `T ≥ T₀` side condition. The
paper's clean `T`-free `2m/T` is exactly what `c₀K = 1` preserves, so the artifact pays the `7 → 8`
in the constant instead. Either way the rate `O(√(L³T log T))` is unchanged: a geometric series
converges for every `c > 0`, which is the bullet above.

**Direction of the hypothesis change.** `hdelta` in `eq39_collapse` / `theorem2_concrete` /
`theorem2_rate` / `theorem3_rate` is `delta l t ≤ √(K₀ log T/ηl l)`, which is *larger* than the
paper's `√(8 log T/ηl l)` by `√(100/88) = 1.066`. A larger right-hand side is an easier hypothesis
to discharge, so this substitution moves the artifact *toward* the paper's Lemma 5, not away from
it: whatever proved the paper's radius proves this one a fortiori, which is the direction required —
the concentration bound the artifact can actually prove (this section's `c₀`) is the one with the
larger radius.

---

## 4. The bridge from the formal bound to Theorem 2's `O(·)`

**The concrete bound is machine-checked; only its restatement as `O(·)` is not.**

`TSDPP.theorem2_concrete` (in `lean4/TSDPP/Theorem2.lean`) is a Lean theorem, sorry-free and
depending only on the three kernel axioms:

  `|BR| ≤ K · 8 · √( L³ · (m·L) · log T / η )`,  `T = m·L`,  `K = C²/2 + (2C²+2CD+C)·L`

What is *not* a Lean theorem is the step from this to the paper's `BR(T) = O(√(L³T log T))`.  That
step is arithmetic on the constant, written out below and carried out by hand.  It is isolated
here so it cannot be mistaken for checked work.

**Derive.** Since `K = C²/2 + (2C²+2CD+C)·L ≤ K'·L` for `K' = C²/(2L) + (2C²+2CD+C)` — a constant
in `T` whenever `C`, `D` are `T`-free (GAP-3, which the paper asserts) — and since
`T = mL` means `m = T/L`, the radicand unfolds exactly:

```
L³ · (m·L) · log T / η  =  L³ · T · log T / η,
```

so

```
K · 8 · √(L³ T log T/η)  ≤  8·K'· √(1/η) · √(L³ · T · log T).
```

That is Theorem 2 immediately, with the explicit constant `c = 8·K'·η^{−1/2}`.  The `8` here is
the artifact's, not the paper's: it is `7 + 1` at the artifact's radius constant `K₀ = 100/11`
(where the paper, at its own `K = 8`, would write `7 = 6 + 1`) — see §3.4.1.  Both give the same
`O(√(L³T log T))`; only the coefficient differs, so nothing in this section depends on which of
the two constants the radius carries.

**Status of each piece — all of it machine-checked.**

| piece | status |
|---|---|
| `|BR| ≤ K·8·√(L³T log T/η)` | **Lean theorem** — `TSDPP.theorem2_concrete` |
| `L³·(mL)·logT/η = L³T logT/η` | arithmetic identity, closed by `ring` inside `theorem2_concrete` |
| `K ≤ K'·L` with `K' = ½C² + (2C²+2CD+C)` | **Lean theorem** — `TSDPP.regretCoeff_le_mul` |
| `|BR| ≤ c·L·√(L³T log T/η)`, `c = 8K'` | **Lean theorem** — `TSDPP.theorem2_rate` |

`theorem2_rate` is the paper's rate with the coefficient `c` written out, and it is obtained from
`theorem2_concrete` by the single application of `regretCoeff_le_mul`.  So there is **no remaining
hand arithmetic in the constant**: every step of §4 is a Lean declaration.

What is *not* formalized is the passage from `c·L·√(L³T log T/η)` to the `O(·)` symbol itself.
That step is bookkeeping over an undefined notion — `O(·)` needs a filter on `T` and a decision
about whether `L` grows with `T` (GAP-4), and the paper commits to neither.  Substituting any
consistent convention into `theorem2_rate` is mechanical; choosing the convention is a modelling
decision, not a mathematical one, and it is left to the reader rather than silently fixed.

---

## 5. Summary of the fidelity verdict

| failure mode | audited in | verdict |
|---|---|---|
| **silently dropped** (a paper item never appears) | §1.0 coverage table | **partly — and this is the largest single caveat in this file.** All 13 numbered *environments* are enumerated and dispositioned. But §1.0.1 shows 8 of the 40 numbered equations are **absent**, and they are not incidental: they are the problem statement itself — P1 (Eq (5)–(7)), the DPP index (Eq (10)), the observation model (Eq (11)), the virtual queue (Eq (12)), the constrained policy (Eq (13)), the index update (Eq (14)) — plus the **definitions** of the value function `J` (Eq (17)) and the Bayesian regret `BR` (Eq (18)). `BR` and `J` enter `theorem2_concrete` as abstract reals satisfying hypotheses, not as defined objects; `cards/R4.md` records that Eq (10), (12), (13) are deliberately out of scope. Nothing is hidden, but the artifact formalizes the paper's *analysis*, not its *problem statement* |
| **too weak** (instance mistaken for the general claim) | §1 per-item table | no — every `∀` in the paper appears as a `∀` in the Lean, with the same domain |
| **vacuous** (unsatisfiable hypotheses) | §2 satisfiability audit | no — every non-trivial hypothesis has an exhibited witness |
| **shifted** (wrong direction / quantifier order) | §1 direction column, §3 | no — the only divergences (§3) are documented, forced, and do not alter the conclusion |
| **axiom smuggling** | `TSDPP/Audit.lean` | no — `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}` for every headline theorem; the two citation nodes are hypotheses, not axioms |
| **the `O(·)` claim itself** | §4 | **yes, up to the notation** — `TSDPP.theorem2_rate` is a machine-checked Lean theorem of the form `\|BR\| ≤ c·L·√(L³T log T/η)` with `c` explicit and `T`-free.  Passing to the `O(·)` *symbol* requires choosing a convention the paper never fixes (GAP-4); that is a modelling decision, not a mathematical gap |

The last row is the honest boundary of this artifact.  Everything the paper *derives* is
machine-checked, up to and including the headline `theorem2_concrete`; what remains by hand is
naming the asymptotic constant, not establishing the rate.

**Also checked, and worth stating:** the headline bound is falsified numerically as well as
proof was trusted — `eq39_collapse` attains `0.889` of its bound and `theorem2_concrete` has zero
violations over a grid at the `hηT` / `hBle` hypothesis boundaries.  This is the same discipline
applied to R9's tight constants in §1, and it is what would have caught a mis-stated (as opposed
to mis-proved) headline.
