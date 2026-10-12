# L5-REFUTATION — the registered Lemma 5 target is FALSE

**Status: CLOSED (machine-checked).**  All five nodes are closed.  The refutation is
`lean4/TSDPP/Lemma5Refutation.lean`, unconditional, audited by `lean4/scripts/check_axioms.sh`; each declaration depends on nothing or on a subset of `{propext, Classical.choice, Quot.sound}`.
This card is the *refutation* counterpart of `L5.md`: that card asks "is the registered target
provable?", this one answers "no, and here is the certificate".

Trap record: `../DESIGN.md` P-64 (the register is false at all), P-67 (it also fails on the paper's
own parameter curve against the paper's own constant), P-68 (the small-`α`/`β` corner admits no
reference but the density itself), P-69 (a figure without its grid is not evidence),
P-70 (an asymptotic criterion quoted as the exact threshold of a finite witness).

---

## 0. SCOPE — what this refutation does *not* say

Written first, because "refutation" invites over-reading and the wrong reading here is a serious one.

**It is a refutation of one lemma's `r ≥ 1` form — not of the paper.**  Three claims must be kept
apart, and they have three different answers:

| # | claim | verdict |
|---|-------|---------|
| 1 | the registered `r ≥ 1` target, `c = 11/100` | **FALSE** — machine-checked, `lemma5_as_registered_is_false` |
| 2 | the **paper's own Lemma 5**, stated for `0 ≤ r ≤ 1` (Eq (31)) | **not refuted — and almost certainly true** |
| 3 | the paper's **theorem** (its regret bound) | **not refuted, and not refutable from what is here** |

Why (2) survives.  The witness sits at `r = 14`, entirely outside the paper's declared range.  On
`0 ≤ r ≤ 1` the paper's bound holds with room: over a sweep of `(α, β, r)` the worst ratio
`Pr(|X−Y| ≥ rE(X)) / (2·exp(−αr²/8))` is **0.393**, and the trend is that larger `α` buys more room
(`(50,1000)` at `r = 1` uses `2e-4` of the budget).  There is also a hard ceiling: as `r → 0⁺` the
left side tends to `1` and the right to `2`, so the ratio tends to `1/2` from below and **that range
cannot be violated at all**.  The refutation's witness family therefore cannot reach it.

Why (3) survives.  **A proof step that does not go through does not make the theorem false.**  What
is established is that Eq (33) applies Lemma 5 at `r = max{1, √(8 log T/α)} ≥ 1`, outside the range
the lemma is stated for — a citation failure, not a propositional one.  The theorem may well be true
by another route.  Refuting it would need a regret counterexample, which needs the problem statement
(Eq (10),(12),(13)) formalized — and this artifact never did that: card `R4` is **NOT FORMALIZED**.

So the honest one-liner is: **the artifact's own registration was wrong, and the paper's *use* of
Lemma 5 is invalid — not that the paper's theory is false.**

Two honest footnotes on how much of this is *proved* versus *argued*:

* That the paper's Lemma 5 is stated for `0 ≤ r ≤ 1` is a **textual** fact (Eq (31)), not a Lean
  theorem.  Nothing in this repo formalizes the paper's prose.
* The `0.393` worst-ratio sweep and the `r → 0⁺ ⟹ ratio → 1/2` ceiling are **numerical and
  analytic arguments, not machine-checked**.  They say the paper's Lemma 5 is *not obviously false*;
  they do not prove it.  This card does not claim it as a Lean result, and no card should.

The reason this bug survived to submission is structural, and worth stating: the true tail exponent
is about `αr²/2` while the paper claims `αr²/8`.  Near `r ≤ 1` the claimed exponent is far *larger*
than the truth, so the bound is comfortably satisfied and looks fine; the gap only opens up at large
`r`.  A constant that is 4× too weak is invisible in exactly the regime the paper checks it in.

---

## 1. Theorem card

**Root statement, as registered** (`lean4/TSDPP/BetaConcentration.lean:7-9`):

> `Pr(|X − Y| ≥ r·α/(α+β)) ≤ 2·exp(−(11/100)·α·r²)`  for `X, Y` iid `betaMeasure α β`, `r ≥ 1`.

**Claim.**  This is **refuted**.  It is a `∀`-statement, so a refutation is a single witness with a
lower bound on the left that exceeds the right.

**Witness chosen for the machine-checked refutation** — `(α, β, r) = (1, 100, 14)`.  This is *not*
the numerically strongest witness (the strongest recorded is `(5,500,10)`, a `1.4e5×` violation);
it is the witness whose **entire proof chain is elementary rational arithmetic**, which is what
makes it Lean-tractable.  The magnitude of the violation is not the point; the existence is.

At `(1, 100, 14)`:  `μ = 1/101`, the event level is `s = rμ = 14/101`, and the registered bound is

```
RHS = 2·exp(−(11/100)·1·14²) = 2·exp(−539/25) = 8.6624544872092589e−10 .
```

The certificate is the elementary containment

```
{X ≥ t} × {Y ≤ u}  ⊆  {|X − Y| ≥ s}        whenever  s ≤ t − u ,
```

used at `t = 15/101`, `u = 1/101` (where `t − u = 14/101 = s` **exactly**), together with the
`Beta(1, B)` tail values

```
Pr(X ≥ t) = (1 − t)^B ,        Pr(Y ≤ u) = 1 − (1 − u)^B .
```

With `B = 100`:

```
LB := Pr(X ≥ 15/101)·Pr(Y ≤ 1/101) = (86/101)^100 · (1 − (100/101)^100)
    = 6.56519042665426123425247426156407646947033476671123883422033e−8
```

and `LB / RHS = 75.7890322696441306875409472590144850859617792213410444485699`.

| quantity | value (20 s.f.) |
|---|---|
| `(86/101)^100` | `1.04161624878569487366264294597932444546702394330102015060257e−7` |
| `(100/101)^100` | `3.69711212329119261179963468473963787987136842954007044881648e−1` |
| `1 − (100/101)^100` | `6.30288787670880738820036531526036212012863157045992955118352e−1` |
| `LB` | `6.56519042665426123425247426156407646947033476671123883422033e−8` |
| `RHS = 2·exp(−539/25)` | `8.66245448720925890175399677784829433757801116315003744541210e−10` |
| ratio | `75.7890322696441306875409472590144850859617792213410444485699` |

Reproduction is §4; these figures were produced by the routine printed there, not by hand and not
by a quadrature — the whole chain is `Fraction` arithmetic plus `exp` at 60 dps.  **[Per P-69 the
routine is part of the figure; a decimal quoted without it does not count as evidence.]**

**Verdict.**  The registered target is false.  `FIDELITY.md` §3.4, `cards/L5.md` and the
`BetaConcentration.lean` header already record this; this card supplies the *certificate*, and
`lean4/TSDPP/Lemma5Refutation.lean` (when it lands) supplies the machine-checked form.

### 1.1 The general form, and the paper's own constant

The certificate does not depend on `11/100` at all.  Written with the constant left free, the
assembly proves

> for **any** `c` with `2·exp(−196·c) < LB`, the bound `2·exp(−c·α·r²)` is false on `r ≥ 1`.

Since `LB = 6.565190426654261234252474e−8`, the hypothesis is `c > log(2/LB)/196 =
0.087918604136904736052…`, so:

**no constant larger than `0.08792` survives on the registered range `r ≥ 1`.**

Two instances are therefore discharged by the same proof:

| theorem | constant | violation certified by `LB` | violation at the true probability |
|---|---|---|---|
| `lemma5_as_registered_is_false` | `11/100 = 0.11` | `75.79×` | `353.479047486012×` |
| `paper_lemma5_range_ge_one_is_false` | `1/8 = 0.125` (the paper's, p. 9) | `1433.61368656713×` | `6686.3553368477×` |

The second is the important one and it is **not** an artifact of the transposed constant: whatever
one concludes about `11/100`, the lemma *as printed* is false on the range Eq (33) applies it to.
This is P-67's content, machine-checked at a single witness rather than sampled along the curve.
(At `α = 1` Eq (33) gives `r = √(8 log T)`, so `r = 14` is its value at `log T = 49/2` — the witness
sits on the paper's own curve, though this card claims only the Lemma-5 statement, not that every
other hypothesis of Theorem 2 holds at `T = e^{49/2}`.)

---

## 2. Proof card — five nodes

**All five nodes are CLOSED.**  The `MainBox.lean` assembly that took `N1` and `N4` as *hypotheses*
has been replaced: in `TSDPP/Lemma5Refutation.lean` those hypotheses are discharged by
`TSDPP.betaMeasure_one_Ici` / `_Iic` and `TSDPP.refute_arith`, so the two headline theorems carry
**no hypotheses at all**.

```
  N1  betaMeasure 1 B (Ioo a b) = ofReal ((1-a)^B - (1-b)^B)     [Beta tail values]
   |    0 <= a <= b <= 1, B >= 1         CLOSED   TSDPP/BetaOneCDF.lean
   |    0 <= t <= 1  ==>  Ici t = ofReal ((1-t)^B)
   |    0 <= u <= 1  ==>  Iic u = ofReal (1 - (1-u)^B)
   |
   +--> N2  (86/101)^100 >= exp(-750/43)                        CLOSED   exp_neg_le_pow_86_101
   +--> N3  (100/101)^100 <= 2/5, i.e. 1-(100/101)^100 >= 3/5   CLOSED   pow_100_101_le
   +--> N4  2*exp(-539/25) < (3/5)*exp(-750/43)                 CLOSED   arith_core
                 <=> exp(4427/1075) > 10/3, from Real.add_one_le_exp
   |
   +--> N4' refute_arith: the residual against LB itself        CLOSED   slack 75.79x

  N5  box containment: s <= t-u ==> {X>=t}x{Y<=u} subset {|X-Y|>=s}   CLOSED
   |
   +--> N0  not (forall a b r, ...)                             CLOSED, UNCONDITIONAL
                TSDPP/Lemma5Refutation.lean -- zero hypotheses
```

Two side conditions on `N1` are **load-bearing, and were found the hard way** (recorded in
`BetaOneCDF.lean`'s header): the `Ici` form needs `t <= 1` as well as `0 <= t`, because for `t > 1`
the left side is `0` while `(1-t)^B` is positive for even `B` and negative for odd -- no single
formula holds; and the `Iic` form needs both `0 <= u` and `u <= 1`.  An earlier brief asked for the
`Ici` form with only `0 <= t`; **that statement is false**, and the extra hypothesis is the fix, not
a convenience.  Both instantiations (`t = 15/101`, `u = 1/101`) sit inside `[0,1]`, so neither is
obstructed.

Slack at each link, all measured rather than eyeballed -- nothing here is delicate:

| node | quantity | slack |
|---|---|---|
| N2 | `(86/101)^100 / exp(-750/43)` | 3.914x |
| N3 | `(2/5) / (100/101)^100` | 1.082x |
| N4 | `(3/5)*exp(-750/43) / (2*exp(-539/25))` | 18.43x |
| N4' | `LB / (2*exp(-539/25))` | **75.79x** |

`N3`'s 1.082x is the tightest link, and it is why the constant is `2/5` rather than something
rounder.  `3/8` **also** closes the chain -- it is the *better* lower bound on `1 - (100/101)^100`,
giving 19.20x at N4' -- but it needs `n = 5` Taylor terms where `2/5` needs `n = 4`
(`sum_{i<4} (100/101)^i/i! = 2.642` clears `5/2` but not `8/3`).  Both were verified to close; `2/5`
was kept because it landed first with fewer terms.  Recorded because a mid-flight re-brief went out
asserting `2/5` was necessary -- it was not.

### N1 — the Beta(1,B) tail values

`betaMeasure α β = volume.withDensity (betaPDF α β)` with
`betaPDFReal 1 B x = (if 0 < x ∧ x < 1 then (1/beta 1 B) · x ^ (1−1) · (1−x)^(B−1) else 0)`, and
`beta 1 B = Γ(1)Γ(B)/Γ(1+B) = 1/B`.  So on `(0,1)` the density is exactly `B·(1−x)^(B−1)`, and

```
betaMeasure 1 B (Ioo a b) = ∫_a^b B(1−x)^(B−1) dx
                          = B∫_{1−b}^{1−a} w^(B−1) dw      (w = 1−x)
                          = (1−a)^B − (1−b)^B .
```

This is the only real-analysis node.  It is a polynomial integral — `B` is a natural number, so
`(1−x)^(B−1)` is a **polynomial**, not a genuine `rpow` — which is the whole reason this witness
was chosen over a numerically stronger one.  **[Note `x^(1−1) = x^0 = 1` is what makes `α = 1`
special: for `α ≥ 2` the density carries a positive power of `x` and the same computation produces
a sum of `α` terms, still elementary but `α` times larger.  `α = 1` is the cheapest instance.]**

*Range caveat.*  The identity `betaMeasure 1 B (Ici t) = (1−t)^B` is **false for `t < 0`** (the
left side is `1`, the right side is `> 1`); group A was told to state the strongest true form it
can close.  We only ever use `t = 15/101`, `u = 1/101`, both in `(0,1)`.

### N2, N3, N4 — the arithmetic

Node N3's constant was chosen after measuring slack.  With `(100/101)^100 = 0.36971121232911926118`
and `1 − (100/101)^100 = 0.63028878767088073882`, the **operational** comparison is the lower one
(`1 − (100/101)^100 ≥ c`), and there the two candidates differ sharply:

| candidate `c` | operational slack `(1 − (100/101)^100)/c` | Taylor terms needed for the `exp` step |
|---|---|---|
| `5/8 = 0.625` | `1.0084620602734091821…` — **0.85%** | `n = 5` (`Σ_{i<4} = 2.641996 < 8/3 = 2.666667`) |
| `3/5 = 0.600` | `1.0504813127848012314…` — **5.05%** | `n = 4` (`Σ_{i<4} = 2.641996 > 5/2 = 2.500000`) |

The weaker constant is the better proof, so `3/5` (from `(100/101)^100 ≤ 2/5`) is the one briefed.
**[Figure discipline, per P-69: the two slacks are quoted as the explicit ratio
`(1 − (100/101)^100)/c`, not as a bare percentage — the percentage differs by a factor of two
depending on which side of the ratio you divide by, and an earlier draft of this card got that
wrong.  This is also why the correction was sent to group C mid-flight: a correction is itself a
claim.]**

Slacks along the chain, all as explicit ratios:

| link | ratio | 
|---|---|
| `(86/101)^100 / exp(−750/43)` | `3.9139159961567850136…` |
| `(1 − (100/101)^100) / (3/5)` | `1.0504813127848012314…` |
| `exp(4427/1075) / (10/3)` | `18.433445974203351667…` |
| `LB / RHS` (overall) | `75.7890322696441306875…` |
| `P_true / RHS` (independent, §4) | `353.47904748601156244…` |

The binding link is N3.  N1 and N5 are exact, not inequalities.

---

## 3. Dependency DAG (what N0 rests on)

```
   N0  (¬ registered target)
    ├── N5  box containment                    CLOSED  prod_Ici_prod_Iic_le_abs_sub
    ├── N1  Beta(1,B) tail values              CLOSED  TSDPP/BetaOneCDF.lean
    │        └── (Mathlib: betaMeasure, betaPDFReal, beta 1 B = 1/B)
    └── N4  arithmetic residual                CLOSED  TSDPP/Lemma5Refutation.lean
             ├── N2  exp(−750/43) ≤ (86/101)^100   CLOSED
             └── N3  (100/101)^100 ≤ 2/5           CLOSED
```

No node is carried as an axiom.  All five are closed, `N0` is closed by substitution, and the
hypotheses that `MainBox.lean` took are gone from the statement.  The shipped theorem is

```lean
theorem lemma5_as_registered_is_false :
    ¬ (∀ (α β r : ℝ), 0 < α → 0 < β → 1 ≤ r →
        ((betaMeasure α β).prod (betaMeasure α β))
          {p : ℝ × ℝ | r * (α / (α + β)) ≤ |p.1 - p.2|}
          ≤ ENNReal.ofReal (2 * Real.exp (-(11 / 100) * α * r ^ 2)))
```

with no hypotheses at all.  Then `Audit.lean` and `lean4/scripts/check_axioms.sh` apply to it unchanged.

---

## 4. Reproduction

```python
# python (base conda), 60 dps.  No quadrature anywhere: Fraction + mpmath.
from fractions import Fraction as F
from mpmath import mp, mpf, exp
mp.dps = 60
def tof(q): return mpf(q.numerator) / q.denominator

f1  = F(86, 101) ** 100          # Pr(X >= 15/101),  X ~ Beta(1,100)
f2  = 1 - F(100, 101) ** 100     # Pr(Y <= 1/101)
LB  = f1 * f2
RHS = 2 * exp(mpf(-539) / 25)
print(tof(LB), tof(RHS), tof(LB) / RHS)
print(tof(f1) / exp(mpf(-750) / 43))     # N2 slack
print(tof(f2) / (mpf(3) / 5))            # N3 slack
print(exp(mpf(4427) / 1075))             # N4, against 10/3
```

The witness chain is also recorded as *exact rational arithmetic* by construction: `f1` and `f2`
are `Fraction`s, so `LB > RHS` is decided by `Fraction` comparison once `RHS` is bounded.  The
Lean proof re-does that comparison with rational bounds on `exp` (`Real.add_one_le_exp`,
`Real.sum_le_exp_of_nonneg`), which is why it needs no numerical evaluation at all.

**Independence — DONE 2026-09-18.**  A second group re-derived every figure above from scratch,
including the *true* value of `Pr(|X−Y| ≥ 14/101)` by exact rational integration (pure `Fraction`,
never touching this card's inequalities), cross-checked against `mpmath.quad` and `sympy` to 20
digits.  **Nothing was refuted; all nine checks CONFIRMED.**  The important addition is the
quantity this card does *not* claim:

| quantity | value |
|---|---|
| `LB` (this card's lower bound) | `6.5651904266542612343e−8` |
| `P_true = Pr(\|X−Y\| ≥ 14/101)` (independent) | `3.061996161029655566e−7` |
| `LB ≤ P_true` | **yes** — `P_true/LB = 4.6639868184145021307` |
| `P_true / RHS` | **`353.47904748601156244`** |

So the true violation at this witness is **353×**, not the `75.8×` that `LB` proves; the gap is the
price of using one-sample tails only.  `r = 14` was chosen so that even the *provable* lower bound
clears the registered bound by `75.8×` — the refutation does not need the true value at all.

The independent group also reconfirmed the original witness `(2, 200, 10)` by exact integration:
`P_true = 8.606640056680760116e−9` against `2·exp(−22) = 5.5789361857378496154e−10`, ratio
`15.427027250612793133` — matching the `8.606640056681e−09` / `15.43` already recorded in
`L5.md`.  Script: `/tmp/verify_refutation.py`.

---

## 5. Rejected routes

Recorded per CLAUDE.md item 4.  Full detail in `../DESIGN.md` (§5 J-11, and traps P-64/P-67).

* **R-A: prove the registered target.**  Impossible — it is false.  Rejected at P-64.
* **R-B: prove the paper's Lemma 5 on its stated range `0 ≤ r ≤ 1`.**  This is *true* (sweep min
  `c_eff = 0.242848 > 1/8`) but **not reachable from this file's toolkit**: the union split needs
  `r ≥ 1`, and the one-sample Gamma–Markov bound degenerates to `1` once the threshold sits at or
  below the mean (`rμ ≤ μ ⟺ r ≤ 1`).  Three sub-routes dead — see J-11.  It would also not rescue
  the paper, since Eq (33) applies the lemma at `r = max{1, √(8 log T/α)} ≥ 1`.
* **R-C: refute with the strongest witness `(5,500,10)`.**  Rejected for *this* purpose only: the
  certificate needs `(1−t)^500`, whose exact rational form is a 500-term binomial.  Elementary but
  not Lean-cheap.  Kept as the numerical record in `L5.md`.
* **R-D: refute via the exact two-sample probability `∫_s^1 f(x)F(x−s)dx`.**  Rejected: this is the
  *actual* value, so it needs the two-sample Beta integral, which is strictly harder than the
  one-sample tails N1 that the box containment already needs.  The containment buys the refutation
  with one-sample information only — that is the whole trick.
* **R-E: refute via `r = 1` and then argue monotonicity in `r`.**  Rejected at P-62/GAP-2e: the
  argument compared *events* while ignoring that the *bound* also shrinks with `r`; it is a
  direction reversal, formally retracted in `../DESIGN.md` GAP-2e.
* **R-F: refute at `α = 1, β = 100, r = 11` (the first `r` the asymptotic criterion allows).**
  Rejected: `r = 12` is the first failing `r`, not `r = 11`.  The `α = 1, β = 100` sweep of the
  *provable* lower bound against the registered RHS:

  | `r` | `LB` | `RHS = 2·exp(−(11/100)r²)` | `LB > RHS` |
  |---|---|---|---|
  | 9 | `1.868708e−5` | `2.7006367e−4` | no |
  | 10 | `6.1894655e−6` | `3.3403402e−5` | no (holds by 5.4×) |
  | 11 | `2.0248967e−6` | `3.3156634e−6` | **no** (holds by 1.64×) |
  | 12 | `6.5413806e−7` | `2.641225e−7` | **yes** (fails by 2.48×) |
  | 13 | `2.0860632e−7` | `1.6884787e−8` | yes (12.4×) |
  | 14 | `6.5651904e−8` | `8.6624545e−10` | yes (**75.8×**) |

  `r = 10` is worth recording because it is the near miss that makes `r = 14` look arbitrary: the
  exact probability there is `2.809651246898e−5` against `2·exp(−11) = 3.341e−5`, so the target
  **holds** (`c_eff = 0.111730 > 0.11`).  `r = 14` is chosen for **margin** (75.8×), not because it
  is the first failure — the first failing `r` at `α = 1, β = 100` is `r = 12`.

  **[CORRECTED 2026-09-18.**  An earlier revision of this bullet read "the failure needs
  `r + 1 > (11/100)·r²`, i.e. `r ≳ 9.6`", an *asymptotic* criterion written as if it were the exact
  threshold.  It is off by one here (`r = 11` still holds) because it drops the
  `1 − (B/(B+1))^B ≈ 0.63` factor, worth `+0.46` in the exponent.  The corrected threshold `r = 12`
  is read off the table above, which is the routine in §4 generalised over `r`; see trap `P-70`.]**
