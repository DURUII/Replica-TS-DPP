# L5-CONVEX — `Beta(a,b) ≤_cx Γ(a, rate a+b)`, proved

**Status: the mathematics is CLOSED; the Lean 4 formalization is OWED.**  Every node of the DAG
below is proved at paper level and none uses a result outside `Γ`-convexity and one-variable
calculus.  No node is formalized yet, so by the project's own standard — non-formal proof and
formal implementation are two independent deliverables, and neither may be declared done before
both pass — **this card does not close Lemma 5.**  What it closes is the search: the statement is
true, the route is found, and the earlier verdict that this route "dies on a bracket" is
superseded (see §5).

Supersedes: `L5.md` §"A second route that also collapses — convex order, and the bracket it dies
on" and §"The finding: three routes, one obstruction".  That obstruction is real for the
*power-series* route those sections describe, and that route does still die.  It is not real for
convex order itself.

Companion cards: `L5.md` (the route record), `L5-REFUTATION.md` (the registered `r ≥ 1` target is
false, machine-checked — untouched by this card; the witness sits at `r = 14`, outside the paper's
declared range).

---

## 1. THEOREM

Let `a, b > 0`, `c := a + b`.  Let `X ~ Beta(a,b)` and `Y ~ Γ(a, rate c)` (shape `a`, rate `c`).
Then

> **`X ≤_cx Y`** — `X` is below `Y` in convex order.

Both have mean `a/c`, so convex order here is exactly the statement

> `∫₀^k (F_X − F_Y) ≤ 0` for every `k > 0`.

## 2. THE REDUCTION THAT MAKES IT ELEMENTARY

Write `f_X` for the Beta density on `(0,1)` and `f_Y` for the Gamma density on `(0,∞)`.  Both carry
the **same** `x^{a−1}` factor, and it cancels:

```
f_X(x)/f_Y(x) = [x^{a−1}(1−x)^{b−1}/B(a,b)] · [Γ(a)/(c^a x^{a−1} e^{−cx})]
              = K · e^{cx} (1−x)^{b−1},        K := Γ(a+b)/(Γ(b) c^a) > 0.
```

Extend `r` to all of `(0,∞)` by `r(x) := 0` for `x ≥ 1` (where `f_X` vanishes).  With
`h := S_X − S_Y` the survival gap,

```
h' = f_Y − f_X = f_Y · (1 − r)        on (0,∞).
```

So **the sign of `h'` is the sign of `1 − r`, and the whole problem is where the elementary
function `r` crosses the level `1`.**  This is the reduction the earlier route missed; it removes
the CDF power series entirely.

Also `h(1) = S_X(1) − S_Y(1) = 0 − S_Y(1) = −S_Y(1) < 0`, and `h(0) = 1 − 1 = 0`.

## 3. THE PROOF

**L1 (`K < 1`).**  `Γ(t+θ)/Γ(t) < (t+θ)^θ` for all `t, θ > 0` — from `ψ(x) < log x` (convexity of
`log Γ` plus the difference quotient `log Γ(x+1) − log Γ(x) = log x`), giving
`log[Γ(t+θ)/Γ(t)] = ∫_t^{t+θ} ψ < ∫_t^{t+θ} log s ds < θ log(t+θ)`.  Take `t = b`, `θ = a`:
`Γ(a+b)/Γ(b) < c^a`, i.e. `K < 1`.  ∎

**L2 (`r`'s shape on `(0,1)`).**  `log r = log K + cx + (b−1) log(1−x)`, so

```
d/dx log r = c − (b−1)/(1−x).
```

* `b ≤ 1`: the derivative is `≥ c > 0`; `r` is **strictly increasing**, from `r(0⁺) = K < 1`.
* `b > 1`: the derivative vanishes exactly at `x_c := (a+1)/c`, which lies in `(0,1)` precisely
  when `b > 1`; `r` **increases on `(0,x_c)` then decreases on `(x_c,1)`**, from `r(0⁺) = K < 1`
  down to `r(1⁻) = 0`.  ∎

**L3 (`r` does cross `1`).**  Suppose `r ≤ 1` on `(0,1)`.  Then `h' ≥ 0` there, so `h` is
nondecreasing on `(0,1)` and `h(1) ≥ h(0) = 0`.  But `h(1) = −S_Y(1) < 0`.  Contradiction.  ∎

So the set where `r` exceeds `1` is nonempty.  By L2 there are therefore `0 < x₁ ≤ x₂ ≤ 1` with

```
r < 1 on (0, x₁) ∪ (x₂, 1),        r > 1 on (x₁, x₂),
```

where `x₂ = 1` in the `b ≤ 1` case (the `(x₂,1)` interval is then empty) and `x₁ < x_c < x₂` in the
`b > 1` case.  Hence

```
h' > 0 on (0, x₁) ∪ (x₂, ∞),        h' < 0 on (x₁, x₂).
```

**L4 (`h` has exactly one sign change, `+ → −`).**

* `h(0) = 0` and `h' > 0` on `(0,x₁)`, so `h(x₁) > 0`.
* `h` is continuous and **increasing on `(x₂, ∞)`** (`h' > 0` there, since `r = 0`), so
  `h(x₂) < h(1) = −S_Y(1) < 0` when `x₂ < 1`, and `h(x₂) = h(1) < 0` when `x₂ = 1`.
  **This step is free** — it is pure monotonicity, no estimate.
* `h` decreases on `(x₁,x₂)` from `h(x₁) > 0` to `h(x₂) < 0`, so it has **exactly one** zero `x₀`
  in `(x₁,x₂)`.
* `h > 0` on `(0,x₀)`: increasing from `0` to `h(x₁) > 0` on `(0,x₁)`, then decreasing to `0` on
  `(x₁,x₀)`.
* `h < 0` on `(x₀,∞)`: decreasing from `0` to `h(x₂) < 0` on `(x₀,x₂)`, then increasing from
  `h(x₂) < 0` to the limit `0` on `(x₂,∞)`.  ∎

**T3 (`X ≤_cx Y`).**  `H(k) := ∫₀^k h = E[X∧k] − E[Y∧k]`, so `H(0) = 0` and
`H(∞) = E[X] − E[Y] = a/c − a/c = 0`.  By L4, `H` is strictly increasing on `(0,x₀)` and strictly
decreasing on `(x₀,∞)`; a strictly unimodal function with `H(0) = H(∞) = 0` is `> 0` in between.
So `H > 0` on `(0,∞)`, i.e. `∫₀^k (F_X − F_Y) = −H(k) < 0` for all `k`; with equal means this is
`X ≤_cx Y`.  ∎

## 4. COROLLARIES — down to the paper's own constant

**T4 ((D+) and (D−) on their full ranges).**  `x ↦ e^{tx}` and `x ↦ e^{−tx}` are convex for every
real `t`, and `E[e^{tY}] = (1 − t/c)^{−a}`, `E[e^{−tY}] = (1 + t/c)^{−a}`.  Hence

```
(D+)   E[e^{tX}]  ≤ (1 − t/c)^{−a}     for 0 ≤ t < c
(D−)   E[e^{−tX}] ≤ (1 + t/c)^{−a}     for all t ≥ 0
```

`(D−)` on the whole half-line is strictly more than `L5.md` was seeking (`t ≤ c/4`), and `(D+)`
holds on the entire interval where its right-hand side is defined.  Both were open; both fall out of
T3 with no further work.  ∎

**T5 (`BetaProdMGFBound`).**  For `0 ≤ t ≤ c/4`, with `u := t/c ≤ 1/4`,

```
E[e^{t(X−X')}] = M_X(t) M_X(−t) ≤ (1−t/c)^{−a}(1+t/c)^{−a} = (1−u²)^{−a},
```

and `−log(1−u²) ≤ 2u²` for `|u| ≤ 1/√2` — from `−log(1−s) = Σ_{n≥1} sⁿ/n ≤ s + s²/(2(1−s)) ≤ 2s`
for `0 ≤ s ≤ 1/2`.  So `(1−u²)^{−a} ≤ e^{2at²/c²}`, which is the residual hypothesis
`BetaProdMGFBound` at `lean4/TSDPP/Lemma5PaperRange.lean:57`.  ∎

**T6 (the paper's own Lemma 5, at the paper's own `1/8`, on the paper's own range).**
`Pr(|X−X'| ≥ r E(X))` with `E(X) = a/c`.  Markov at `t` and T5 give
`Pr(X−X' ≥ ra/c) ≤ e^{2at²/c²} e^{−tra/c}`; minimising over `t` gives `t = rc/4`, exponent
`2a(rc/4)²/c² − r·(a/c)·(rc/4) = ar²/8 − ar²/4 = −ar²/8`.  The same bound holds for `X' − X` by
symmetry, so the union of the two events costs the factor `2`:

```
Pr(|X − X'| ≥ r E(X)) ≤ 2 e^{−a r²/8}        for all 0 ≤ r ≤ 1.
```

The range is exactly the paper's (`paper.pdf` p. 9 Eq (31)), and it is exactly what T5's hypothesis
`t ≤ c/4` becomes at `t = rc/4`: `r ≤ 1`.  **No slack is spent anywhere on this chain.**  ∎

## 5. WHAT THIS CORRECTS

`L5.md` recorded that convex order "does not close", because expanding both CDFs as power series in
`s` leaves `F_X − F_W = (s^a/Γ(a+1))·Σ_{n=0}^{b−1} (−1)ⁿ wₙ sⁿ` with `wₙ` non-monotone, so Leibniz
does not apply.  That record is correct **about that expansion**, and that expansion is a dead end.

It is not correct about convex order.  The density ratio `r` is elementary (L2), the sign of `h'` is
the sign of `1 − r` (§2), and the one step that looked like it needed a hard estimate — `h(x₂) < 0`
— is monotonicity plus `h(1) = −S_Y(1) < 0` (L4).  The CDF series never has to be summed.

The same correction applies to `(C')` `(c−t)Var_t(X) ≤ E_t(X)`: it is now a **corollary** of T3 via
the exponential-family identities (`ψ' = −E_t[X] + (c−t)Var_t(X)`), not an independent conjecture, and
its zero numerical slack in the degenerate corner is a property of a proved statement rather than a
reason to doubt it.

## 6. NUMERICAL EVIDENCE (supporting, not load-bearing)

Every number below was computed with cancellation-free evaluators validated **bit-for-bit** (`==` at
80+ digits, not "close to") against elementary closed forms before being used.  See P-19…P-22 in
`lean4/TSDPP/Lemma5PaperRange.TRAPS.md` for why that order is mandatory.

| what | cells | result |
|---|---|---|
| `h` sign change (L4) | 20 pairs, 1461-point gap-free grid | exactly one `+ → −`, 20/20; `(1,1)` crossing matches the closed form to all 25 digits, `0.7968121300200200461615209` |
| `(C')` `ψ' ≤ 0`, second differences | 1120 | 0 violations; worst `−1.27e−16` at `(0.001, 1e5, u=−0.99)` |
| `ψ` nonincreasing, direct evaluation, `dps=150`, no second difference | 5 pairs × 9 `t` | monotone throughout; error floor `~1e−115` vs observed gaps `~6e−14` |
| `(D−)` full range `0 ≤ t ≤ 30c` | 112 | 0 violations; margin **largest** at `u=30`, **smallest** at `u=0.25` — the tight end is exactly where the paper needs it |
| `∫₀^k h ≥ 0` (T3 directly) | — | **no result** — the delegated check stalled (600 s with no progress) and never produced output; T3's only numerical support to date is the row above it, which tests the sign change rather than the integral |

Two hand-derivations were produced, checked numerically, and **discarded as wrong**; both are
recorded so they are not re-derived.  (i) The asymptotic `E_t[X] ≈ a/(b−t)` predicts
`(c−t)Var_t − E_t = a²/(b−t)² > 0`, i.e. `(C')` false — the true value is `−7e−17`, opposite in
sign; the `(1−x)^{b−1} ≈ e^{−bx}` substitution is too crude once the tilt is applied.  (ii) The
reading of `u = 0.96` from the earlier range probe as "`(D−)` stops holding" is an artifact of that
probe's evaluator, not a property of `(D−)` (this table's row 4).

## 7. DAG

```
L1  Γ(t+θ)/Γ(t) < (t+θ)^θ        [CLOSED, elementary]
 │
 └─ K < 1
     │
L2  shape of r on (0,1)            [CLOSED, elementary]
     │
L3  {r > 1} ≠ ∅                    [CLOSED, from h(1) = −S_Y(1) < 0]
     │
L4  h: exactly one sign change, + → −   [CLOSED]
     │
T3  X ≤_cx Y                       [CLOSED]
     │
T4  (D+) and (D−), full ranges     [CLOSED]
     │
T5  BetaProdMGFBound               [CLOSED]
     │
T6  paper's Lemma 5, 1/8, 0 ≤ r ≤ 1     [CLOSED — at paper level]
     │
     └─ OWED: Lean 4 formalization of T3…T6, no `sorry`
        OWED: Lean 4 formalization of L1…L4
```

## 8. OPEN

1. **The Lean 4 artifact.**  Nothing above is machine-checked.  This is the whole remaining distance
   to the deliverable, and it is not small: the chain needs `h`, `r`, the survival functions, the
   convex-order characterization (or a direct stop-loss argument avoiding it), and the Markov step.
   `L5-REFUTATION.lean` and `Lemma5PaperRange.lean` are the existing anchors for what is already in
   Mathlib and what is not (`₁F₁` is not; see P-17).
2. **The `b ≤ 1` / `b > 1` split in Lean.**  L2's case analysis is where the formalization will
   either be short or will need a real `log`/monotonicity development; `x_c = (a+1)/c ∈ (0,1) ⟺ b > 1`
   is the load-bearing arithmetic.
3. **T3's convex-order characterization.**  The route as written uses the standard
   `X ≤_cx Y ⟺ ∫₀^k F_X ≤ ∫₀^k F_Y (∀k) + equal means`.  Whether Mathlib carries that in the exact
   form needed, or whether the stop-loss route (`E[(X−k)_+] ≤ E[(Y−k)_+]`, then a Tonelli
   representation of convex `φ`) is shorter, is not yet determined — this is an API question, and
   P-17's lesson applies: settle what exists before planning the proof.
