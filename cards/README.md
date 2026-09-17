# Cards — theorem cards, proof cards, and the dependency DAG

One file per card.  A card is **CLOSED** only when (a) its Lean declaration builds with no
`sorry`, and (b) `#print axioms` returns a subset of `{propext, Classical.choice, Quot.sound}`.
Every card below records the cards it *consumes*, and — this is the point of the DAG — **which
of its dependencies are still open**, so a reader can see at a glance how much of a result rests
on unproved ground.

The status board in `../DESIGN.md` §3 is regenerated from `lake build` output; this directory is
the human-readable expansion of it.

## DAG

```
                    R1 ──────────────────┐
                                         ├──► R12a ──── (δ ≤ C hypothesis) ──┐
                    R2 ──────────────────┘                                   │
                     │                                                       │
                     └──► R5 ──► R6 ─────────────────────────────┐          │
                                                                 │          │
                    R8 ──► R9 (Lemma 2) ─────────────────────────┤          │
                                    ▲                             │          │
                    R3 ──► R15 ────┘                             │          │
                                                                  ▼          ▼
                                         R10  (Eq 36, Eq 37)  ◄──────────────┘
                                                  │
                    R11 (Eq 38 assembly) ◄────────┘
                                                  │
     R7 (Thm 1) ──────────────────────────────────┤
                                                  ▼
     R14 (Eq 39) ─────────────────────────────► R16  ──►  R17 = ROOT (Theorem 2)
                                                  ▲            ▲
     R13 (Eq 40) ─────────────────────────────────┘            │
                                                                │
     R11 (Eq 38 assembly) ──────────────────────────────────────┘

  Open dependency (carried as a hypothesis, never as an axiom):
     L34 = Lemma 3 + Lemma 4  ([28])   ──► consumed by R11     ** partly — see below **
     L5  = Lemma 5            ([45])   ──► consumed by R13 and R16

  Out of scope (no Lean node at all — see R4.md):
     P1 = Eq (5)–(7)   ─┐
     R4 = Eq (10),(12),(13) ─┴─► the constrained policy; stands in for by the
                                 *hypotheses* of `theorem2_rate`, not by a node
```

`L34` — the paper's Lemma 3 + Lemma 4 — is **partly** discharged.  The two halves must be reported
separately, because the three declarations that carry it do not all carry the same weight:

* **Lemma 3's combinatorial half is a theorem.**  `sum_range_blocks` cuts the horizon `T = m·L`
  into `m` blocks of `L`, and `regret_decomp_episodeOf` supplies Eq (27)'s telescoping, so
  `hdecomp` is *derived* — **in `theorem3_rate`**, which calls `theorem2_rate` at
  `BR := ∑ s ∈ range (m*L), r s` and closes the premise at that instantiation.  `Theorem2.lean`'s
  general `theorem2_rate` still takes `hdecomp` as a premise, by design: it is the statement over an
  abstract `BR : ℝ`.  `Decomp.lean` is explicit that Lemma 3's *other* half — linearity of `∫` over
  a finite index set — is not removed by any of this: *"what disappears is the assumption that the
  decomposition holds, not the assumption that there is something to decompose."*
* **Lemma 4 is proved, and in its most general form** — but it is not wired in, and `hper` is still
  assumed.  `simulation_lemma` telescopes `∫ ω, ΔJ 0 ω ∂μ = ∑ t ∈ range L, ∫ ω, g t ω ∂μ` over an
  **arbitrary** measure space, with `bellman_step_le` supplying its Bellman recursion `hrec`; there
  is no bandit content in either.  What is missing is the instantiation: `Theorem2.lean` imports
  `Mathlib, Decomp, Regret, Assembly, Tail, Rate` — **not `Simulation`** — and `hper` remains a
  *hypothesis* of both `theorem2_rate` and `theorem3_rate`.  `Simulation.lean`'s own card is
  accurate where this table was not: it claims to discharge "*part of* `hper`", not all of it.  The
  missing step is the model — the trajectory law `P_{θ*}` and the posterior samplings `θ^l ∼ Q^l`,
  i.e. `DESIGN.md` **GAP-7** — and not the lemma.

  (`R4` is a **different** absent cluster — the constrained policy of Eq (10),(12),(13), tabulated
  under "Out of scope" above — and nothing in the DAG consumes it.  It is not the blocker here; do
  not merge the two.)

The citation node survives in the DAG above so a reader can see where it *was* — and, for the
`hper` half, where it still **is**.

`L5` is the only remaining open **citation** in the DAG.  (`L34`'s `hper` half is open as a
*hypothesis*, but its mathematical content is proved; the two are different kinds of open and are
counted separately.)  It is never an `axiom`: every Lean
statement that would need it takes it as an *explicit hypothesis*, so a reader can see exactly what
is assumed and where.  See `../DESIGN.md` GAP-2 for the current state — the union-bound route is
proved to have ceiling `0.8839970429 = e/(e−1)·e^{−1/(e−1)}`, whose `−log` is `0.123302 < 0.125`,
so the artifact carries `c = 11/100` rather than the paper's `1/8`, with the difference quantified
in `../FIDELITY.md` §3.4.

**`L5` is being closed now** (card `L5.md`).  Its sub-DAG, all of it proved or in flight:

```
  TSDPP.gammaMeasure_prod_ratio      (set-level Beta–Gamma ratio law)   CLOSED  BetaGamma.lean
        │
        ├──► gamma_ratio_isBetaMeasure  (map-level, via ext_of_Ici)   CLOSED  GammaRatioMap.lean
        │           │
  TSDPP.gammaMeasure_lintegral_exp      (Gamma Laplace transform)       CLOSED  GammaMGF.lean
        │           │
  TSDPP.gammaMeasure_prod_meas_le       (Markov on the product measure) CLOSED  TSDPP/
        │           │
  TSDPP.betaMeasure_Ici_le / _Iio_le    (the two one-sample tails)      CLOSED  TSDPP/
        │           │
  TSDPP.unionWitness                    (two-case numeric witness)      CLOSED  TSDPP/
        │           │
        ▼           ▼
  betaMeasure_abs_sub_concentration     (Eq (31) at c₀ = 11/100)        #10 in progress
```

Two consequences of closing `L5` that reach beyond it:

1. **Promotion (#8) — DONE.** `Scratch/BetaGammaChernoff.lean` and `Scratch/UnionBound.lean` were
   closed but lived outside `TSDPP/`, so they were not in the root module's import closure and not
   audited.  Promoted to `TSDPP/BetaGammaChernoff.lean` and `TSDPP/UnionBound.lean`, verified with
   `lake build TSDPP.BetaGammaChernoff TSDPP.UnionBound` (green, 8933 jobs).
   **This turned out to be a prerequisite of #10, not a follow-on:** `lakefile.toml` declares exactly
   one `lean_lib` (`name = "TSDPP"`) and `Scratch/` has no oleans, so `import Scratch.BetaGammaChernoff`
   cannot resolve at all.  The assembly file would have had no way to reach the lemmas it consumes.
   Checked before moving: no declaration-name conflicts anywhere in `TSDPP/`.
2. **The constant must propagate (#12) — DONE.** The paper's `8` is *coupled* — it appears both in
   Lemma 5's exponent and in the radius `r = √(8 log T/α)`.  Our `c₀` forces `K ≥ 1/c₀ = 100/11` in
   `Rate.lean` and `cη` (the parameter `c`, paper `1/8`, artifact `11/100`) in place of `η/8` in
   `Tail.lean`.  `R13` and `R16` were *true as stated* but were not the statements the chain
   consumes; they have now been **re-stated** at `K₀ = 100/11` (`Tail.lean`'s exponent is the
   parameter `c`, `Rate.lean`'s radicand is `(100/11)`, `two_mul_sqrt_eight_le` is renamed
   `two_mul_sqrt_ratio_le`, and the final constant rose `7 → 8`, near-tight at
   `2√(100/11) + 1 = 7.030227`).  Verified: `lake build TSDPP` green (8953 jobs);
   `scripts/check_axioms.sh` audits 79 declarations, each depending on nothing or on a subset of
   `{propext, Classical.choice, Quot.sound}`.  The rate `O(√(L³T log T))` is unchanged —
   a geometric series converges for every `c > 0`.

`R4` is not an *open* node but an **absent** one — the paper's problem statement was never
formalized, so nothing in the DAG consumes it.  `R4.md` records it in place of the file that would
otherwise be missing.

| card | file | status |
|------|------|--------|
| R1  | `R1.md`  | CLOSED |
| R2  | `R2.md`  | CLOSED |
| R3  | `R3.md`  | CLOSED |
| R4  | `R4.md`  | **NOT FORMALIZED** — Eq (10),(12),(13); the constrained policy.  Out of scope, not an axiom |
| R5  | `R5.md`  | CLOSED |
| R6  | `R6.md`  | CLOSED |
| R7  | `R7.md`  | CLOSED |
| R8  | `R8.md`  | CLOSED |
| R9  | `R9.md`  | CLOSED |
| R10 | `R10.md` | CLOSED |
| R11 | `R11.md` | CLOSED |
| R12a| `R12a.md`| CLOSED |
| L34 | (citation, [28]) | **PARTLY** — L3's combinatorial half is derived (`regret_decomp_episodeOf`, used by `theorem3_rate`); L4 is *proved* (`simulation_lemma`, `bellman_step_le`) but **not instantiated**, so `hper` is still a hypothesis.  Blocked on GAP-7, not R4 |
| L5  | (citation, [45]) | **NOT CLOSED — the registered form is FALSE** (trap P-64, see `L5.md`).  The artifact stated `r ≥ 1`; the paper states `0 ≤ r ≤ 1`.  On `r ≥ 1` the bound fails at `(α,β,r) = (2,200,10)`: exact `8.6066e−09` vs bound `2.7895e−10`.  Everything *delivered* is real and stays: the conditional `hnum ⟹ bound`, the two exact one-sample Chernoff tails, the union-bound core, and the four `'`-forms.  Ratio law **CLOSED** (`BetaGamma.lean`); map-level weld **CLOSED** (#9, `GammaRatioMap.lean`); constant propagation to R13/R16 (#12) **DONE**.  The old ceiling claim (`0.123302 < 1/8` ⟹ `c₀ = 11/100`) is **RETRACTED** (P-62 layers 1–3) and `c₀ = 11/100` is now **[UNDERIVED]**; see `DESIGN.md` J-11 for why restating on the paper's range does not repair the paper's application either.  **Extended by P-67**: on Eq (33)'s own parameter curve `r = max{1,√(8 log T/α)}`, the **paper's** `1/8` fails in 5 of 6 sampled tuples (incl. `α=1, T=10⁶`), so the paper's *use* is false on the paper's own settings, not just the artifact's formalization.  **The refutation is itself now a deliverable** (`CLAUDE.md` item 1 admits "完整证明**或反证**"): card **`L5-REFUTATION.md`** carries the certificate — witness `(α,β,r) = (1,100,14)`, elementary containment `{X ≥ 15/101} × {Y ≤ 1/101} ⊆ {\|X−Y\| ≥ 14/101}`, provable lower bound `LB = (86/101)^100·(1−(100/101)^100)` exceeding the registered bound by **75.79×** (and the true probability by **353.48×**).  Machine-checked form: **`lean4/TSDPP/Lemma5Refutation.lean` — CLOSED, unconditional, audited.**  Both headline theorems (`lemma5_as_registered_is_false` at `11/100`, `paper_lemma5_range_ge_one_is_false` at the paper's own `1/8`) carry **no hypotheses**; their analytic input is `lean4/TSDPP/BetaOneCDF.lean` (the closed-form `Beta(1,B)` tail).  Built into the root closure and audited by `scripts/check_axioms.sh` (90 declarations).  **SCOPE — read `L5-REFUTATION.md` §0 before quoting this:** the **`r ≥ 1`** statement is refuted; the paper's own Lemma 5, which p. 9 Eq (31) states for **`0 ≤ r ≤ 1`**, is **not** refuted (the witness sits at `r = 14`, outside that range), and neither is the paper's theorem — a proof step that does not go through does not make a theorem false |
| R13 | `R13.md` | CLOSED (re-stated at the tail-exponent parameter `c > 0` — #12) |
| R14 | `R14.md` | CLOSED |
| R15 | `R15.md` | CLOSED |
| R16 | `R16.md` | CLOSED (re-stated at `K₀ = 100/11`; final constant `8` — #12) |
| R17 | `R17.md` | CLOSED (**ROOT** — Theorem 2 assembled) |
