# Lean traps hit while closing `TSDPP/Tail.lean`

Card: the first half of paper Eq (40) (sub-piece of R14).
Module: `lean4/TSDPP/Tail.lean`. Toolchain `leanprover/lean4:v4.35.0-rc2`, vendored Mathlib
`f61f3ed7633ff99ecaae4a086395b501652a76ee`.

Every entry is symptom -> cause -> fix, with the error text copied verbatim from
`lake env lean TSDPP/Tail.lean`.

> **Historical note.** These transcripts predate the parameterisation of the exponent
> constant. `Tail.lean`'s two declarations now carry a parameter `c : ℝ`, `0 < c`, and their
> exponents read `c * η * ((l : ℝ) + 1)` / `c * η` where the transcripts below show the literal
> `η / 8` (the paper's value, which is now the instance `c = 1/8`). The *names*
> (`geom_exp_sum_le`, `tail_sum_le`) and the *shape* of every trap are unchanged — each is about
> `Real.exp_nat_mul`'s argument order, `geom_sum_mul_neg`'s monoid power, or `Finset.sum`
> distributivity, none of which depends on the value of the constant. Read `η / 8` below as
> "`c * η` at the value the file used at the time". See `DESIGN.md` P-48 and `cards/R13.md`.

---

## T1 — `∑` distributivity: `sum_mul` / `mul_sum` have *both* a direction and a side

**Symptom.** After rewriting with `Real.exp_nat_mul` I wanted
`∑ l, r^(l+1) = r * ∑ l, r^l`; with the RHS phrased as `(∑ l, r^l) * r` I wrote

```lean
rw [← sum_mul]
```

and got

```
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ∑ i ∈ ?s, ?f i * ?a
in the target expression
  ∑ l ∈ range N, Real.exp (-(η / 8)) ^ (l + 1) = (∑ l ∈ range N, Real.exp (-(η / 8)) ^ l) * Real.exp (-(η / 8))
```

**Cause.** I had the direction backwards. `Finset.sum_mul` is

```lean
Finset.sum_mul (s : Finset ι) (f : ι → R) (a : R) : (∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a
```

i.e. the *product of a sum* is the LHS, the *sum of products* is the RHS. So the forward
`rw [sum_mul]` matches `(∑ …) * a` and the reverse `rw [← sum_mul]` matches `∑ …, f i * a`.
I wanted to go from `∑ …, r^l * r` to `(∑ …, r^l) * r` — that is the forward direction.

**Fix.** `rw [sum_mul]`, then close the residual `∑ l, r^(l+1) = ∑ l, r^l * r` by
`exact sum_congr rfl fun l _ => pow_succ _ _`. (`Finset.mul_sum` is the mirror image,
`a * ∑ i, f i = ∑ i, a * f i`, and I did need that one — see T3.)

---

## T2 — `field_simp`-style rewrites: `one_div` destroys the `1 / ?y` pattern

**Symptom.** Closing `(1 / (1 - exp(-(η/8)))) * exp(-(η/8)) = exp(-(η/8)) / (1 - exp(-(η/8)))`
with `rw [one_div, mul_comm, mul_one_div]` gave

```
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ?x * (1 / ?y)
in the target expression
  Real.exp (-(η / 8)) * (1 - Real.exp (-(η / 8)))⁻¹ = Real.exp (-(η / 8)) / (1 - Real.exp (-(η / 8)))
```

**Cause.** `one_div` is `1 / a = a⁻¹` and rewrites *every* occurrence, so it cannot be used
to normalise a goal in which a later tactic still needs to recognise the `1 / _` *notation*.
After `rw [one_div, mul_comm]` the LHS had already become `exp(…) * (1 - exp(…))⁻¹`, and
`mul_one_div` — whose pattern is literally `?x * (1 / ?y)` — had nothing left to bite on.
Note `mul_one_div` and `div_eq_mul_inv` are *different lemmas about the same fact*; the
former is notation-sensitive, the latter is not.

**Fix.** Dropped all three rewrites and used `by ring`. This is safe here because the goal is
a pure inverse-multiplication identity (`a * (b * c⁻¹) = a * b * c⁻¹`) needing **no**
cancellation and **no** nonzero side condition, so `ring` is not being asked to divide by a
possibly-zero denominator. This is the *opposite* of the trap already recorded in the project
(`field_simp` closing the goal so that a trailing `ring` errors with
`No goals to be solved`): here `field_simp` would have *over*-normalised. `ring` is the
tactic to reach for on the identity itself; `field_simp` only when a hypothesis is needed.

---

## T3 — `rw [mul_sum]` fires on the *outer* occurrence, not the one you meant

**Symptom.** Stepping from `(L : ℝ) * ∑ l, 2 * f l` to `(L : ℝ) * (2 * ∑ l, f l)` I wrote
`rw [mul_sum]` and the goal became

```
⊢ ∑ i ∈ range N, ↑L * (2 * Real.exp (-(η * (↑i + 1)) / 8)) = ↑L * (2 * ∑ l ∈ range N, Real.exp (-(η * (↑l + 1)) / 8))
```

— the rewrite had fired on the *outside* `(L : ℝ) * ∑ …`.

**Cause.** `rw` rewrites **all** matching subterms, outermost ones included, and
`Finset.mul_sum (s) (f) (a) : a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i` matches
`(L : ℝ) * ∑ l, 2 * f l` directly with `a := (L : ℝ)`. The occurrence I wanted to rewrite
(`∑ l, 2 * f l` on its own, read as `2 * ∑ l, f l`) is *not* of the form `?a * ∑ …`, so it
was never a candidate in the first place. The rewrite did exactly what it was told; my
intent was the problem.

**Fix.** Name the inner identity in its own `have`, where it is the whole goal and no outer
match exists:

```lean
have htwo : ∑ l ∈ range N, 2 * Real.exp (-(η * ((l : ℝ) + 1)) / 8)
    = 2 * ∑ l ∈ range N, Real.exp (-(η * ((l : ℝ) + 1)) / 8) := by
  rw [mul_sum]
```

and then `rw [htwo]` in the `calc`, which can only match the inner sum. **General rule for
this file: never `rw` a distributivity lemma in a goal that has a nesting it could reach;
hoist the intended step into a `have` first.**

---

## T4 — `Real.exp_nat_mul` puts the *natural number on the left* of the product

**Symptom.** Not an error, a near-miss. The key identity
`exp(-(η(l+1))/8) = exp(-(η/8))^(l+1)` is tempting to attack with
`Real.exp_mul : exp (x * y) = exp x ^ y`, setting `y := (l+1 : ℕ)`.

**Cause.** `Real.exp_mul` takes a **real** exponent and produces `rpow`, so it yields
`exp (-(η/8) * ↑(l+1))`, i.e. `Real.exp`'s *real* power. What the sum needs is the *monoid*
power `Real.exp (-(η/8)) ^ (l+1)` so that `pow_succ` / `geom_sum_mul_neg` apply. The right
lemma is

```lean
Real.exp_nat_mul (x : ℝ) (n : ℕ) : Real.exp (↑n * x) = Real.exp x ^ n
```

and the gotcha is that the cast is on the **left**: the LHS is `↑n * x`, *not* `x * ↑n`.
Rewriting backwards from the goal therefore requires the goal's exponent to already be
`↑(l+1) * -(η/8)`, which it is not — the goal has `-(η * (↑l + 1)) / 8`.

**Fix.** `rw [← Real.exp_nat_mul (-(η / 8)) (l + 1)]`, then `congr 1`, `push_cast`, `ring`
to reconcile `-(η * (↑l + 1)) / 8` with `↑(l + 1) * -(η / 8)`. The `push_cast` is load-bearing:
without it `ring` sees `↑(l + 1)` as an opaque atom and cannot relate it to `↑l + 1`.

---

## T5 — `lake env lean` on an audit file needs the `.olean` to exist first

**Symptom.**

```
error: object file '<repo-root>/lean4/.lake/build/lib/lean/TSDPP/Tail.olean' of module TSDPP.Tail does not exist
```

**Cause.** `lake env lean TSDPP/Tail.lean` **elaborates** the file but does not write an
`.olean`. `import TSDPP.Tail` in a second file needs the compiled artefact, which only
`lake build` produces. The initial `lake env lean TSDPP/Tail.lean` succeeding is therefore
*not* evidence that `import TSDPP.Tail` will work.

**Fix.** `lake build TSDPP.Tail` (a single-module target, not the whole project) before
running any `import TSDPP.Tail` audit. Building `TSDPP.Tail` replayed the imported Mathlib
oleans as `[8931/8931]`, which is expected and not a sign that the whole project was built.

---

## T6 — workflow trap: a placeholder `exact le_refl _` fails with a *typeclass* error

**Symptom.** While probing the proof state after a `show`, I used `exact le_refl _` as the
last line. The error is not about `le_refl` at all:

```
error: typeclass instance problem is stuck
  Preorder ?m.259

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `Preorder` is a metavariable.
```

**Cause.** `le_refl _` leaves the type metavariable-free enough for `le_refl`'s implicit
`α` but not for the `[Preorder α]` instance, so the error surfaces as a stuck instance
rather than as "wrong lemma". It reads like a *statement* problem and sends you looking at
the theorem statement, which is fine.

**Fix.** Read it as "placeholder, not a statement bug" and continue. If a real placeholder is
wanted for state inspection, prefer `trace_state` (which leaves the goal intact) over a bogus
closer. The useful signal here is that **all the `have`s above the placeholder elaborated**,
which is how the file was built incrementally: keep the previous placeholder and watch the
error line number move down.

---

## T7 — process trap: never cite a `GAP-`/`R-` number without reading `DESIGN.md`

**Symptom.** My first draft of the module docstring said "GAP-4 in `DESIGN.md` records what is
not here". `DESIGN.md` has no card for Eq (40), and its actual **GAP-4** is "the exponent in
Eq (19)" — an unrelated topic. **R15** is also already taken (Eq (35) cancellation,
`TSDPP.Round.round_diff_identity`).

**Cause.** The card numbering was assumed from context instead of read.

**Fix.** Read the card table in `DESIGN.md` (read-only — it is not this card's file to edit)
before naming any cross-reference, and prefer describing the un-formalized steps in prose over
inventing a number. The docstring now says "a sub-piece of card R14" and lists the three
un-formalized steps by content.

---

## Mathematical notes (not Lean traps, but recorded here for `DESIGN.md`)

* **`hη : 0 < η` is genuinely necessary** and cannot be dropped from either statement. At
  `η = 0` the right-hand side is `Real.exp 0 / (1 - Real.exp 0) = 1 / 0 = 0` (in a field
  `x / 0 = 0`), while the left-hand side at `N = 1` is `Real.exp 0 = 1`; `1 ≤ 0` is false.
  Verified in Lean: both `Real.exp 0 / (1 - Real.exp 0) = (0:ℝ)` and
  `¬ ((1:ℝ) ≤ Real.exp 0 / (1 - Real.exp 0))` close by `norm_num`.
* **The bound is asymptotically sharp**, so the paper's constant `1/(1 - e^{-η/8})` is not
  lossy. Independent numeric check (`python`, base conda env) of
  `Σ_{l<N} exp(-η(l+1)/8) ≤ e^{-η/8}/(1 - e^{-η/8})`:

  | `η` | LHS at `N = 1000` | RHS |
  |-----|-------------------|-----|
  | 0.05 | 159.1926123928217 | 159.50052083299352 |
  | 0.5 | 15.505207994280665 | 15.505207994280672 |
  | 1.0 | 7.510413955001841 | 7.5104139550018445 |
  | 3.0 | 2.1978436688506173 | 2.1978436688506178 |
  | 8.0 | 0.5819767068693265 | 0.5819767068693265 |

  The gap vanishes as `N → ∞`, i.e. the finite partial sum converges to the bound from
  below — the expected behaviour for a geometric series, and a check that the index shift
  `l ↦ l + 1` was applied on the correct side.
* **Eq (40) as printed is suspect.** `paper.txt` renders the first inequality of the chain as

  `Σ_{l=1}^{m} Σ_{t=1}^{L} 2e^{-α^l_{A_t} r^l_{A_t}/8} ≤ n Σ_{l=1}^{n} Σ_{t=1}^{L} 2e^{-α^l_{A_t}/8} + 2m/T`

  with a leading `n` on the middle sum. `n = ⌈8 log T/η⌉` is the truncation index, and a
  factor of `n` (which grows with `T`) would destroy the `1/(1 - e^{-η/8})` conclusion two
  steps later. The only reading under which the displayed geometric factor is correct is
  `≤ Σ_{l=1}^{n} Σ_{t=1}^{L} 2e^{-α^l_{A_t}/8} + 2m/T`. This is almost certainly an OCR
  artefact (or a typo in the preprint), not a real `n` factor; **the card formalizes the
  geometric arithmetic that is common to both readings**, and is therefore unaffected either
  way.
