# Finding and scope

The bound used in the application of Lemma 5 in
[Zhou et al., INFOCOM 2026](https://doi.org/10.1109/INFOCOM59046.2026.11571737)
fails for some parameters outside the lemma's stated range. The artifact registered an extended
statement as its verification target; Lean refutes both that target and the extension with the
constant stated in the paper.

Three statements must be distinguished:

| Statement | Finding |
| --- | --- |
| Lemma 5 as stated in Eq. (31), for `0 ≤ r ≤ 1` | Not refuted by these counterexamples |
| The extended bound for `r ≥ 1`, with `c = 11/100` or `c = 1/8` | Refuted in Lean |
| The application in Eq. (33), at `r = max{1, √(8 log T/α)}` | For `r > 1`, not justified by Lemma 5 as stated |

This identifies a gap in the derivation of the claimed regret bound. It does not refute the
paper's main theorem.

## Counterexample

Because the extended statement is universally quantified, a single counterexample suffices to
refute it. Let `X, Y` be independent `Beta(1, 100)` variables. At `(α, β, r) = (1, 100, 14)`:

```
{X ≥ 15/101} × {Y ≤ 1/101} ⊆ {|X − Y| ≥ 14/101}
LB = (86/101)^100 · (1 − (100/101)^100)
```

The containment gives a probability lower bound using two one-sample tails. Write `LB` for this
certified lower bound, `P` for the actual two-sample probability, and
`B_c = 2 exp(−cαr²)` for the claimed upper bound.

| Quantity | Value at `(1, 100, 14)` |
| --- | --- |
| `LB` | `6.5652 × 10⁻⁸` |
| `P` | `3.0620 × 10⁻⁷` |
| `B_(11/100) = 2 exp(−539/25)` | `8.6625 × 10⁻¹⁰` |
| `B_(1/8) = 2 exp(−49/2)` | `4.5795 × 10⁻¹¹` |

| Constant `c` | Certified ratio `LB / B_c` | Actual ratio `P / B_c` |
| --- | --- | --- |
| `11/100` (registered target) | `75.79` | `353.48` |
| `1/8` (paper) | `1433.61` | `6686.36` |

Both certified ratios exceed one, which is sufficient for the Lean refutations. The values of
`P` come from separate exact rational integration, recorded in
[cards/L5-REFUTATION.md §4](cards/L5-REFUTATION.md#4-reproduction); they are not needed by the
Lean proofs. Decimal values and ratios are rounded.

A further numerical counterexample, `(2, 200, 10)`, gives `P = 8.6066 × 10⁻⁹`, whereas
`B_(11/100) = 2 exp(−22) = 5.5789 × 10⁻¹⁰`; the ratio is `15.43`.

## The two Lean refutation theorems

The declarations establish that each extended statement is false, rather than merely recording
an unsuccessful proof attempt.

| Declaration | Statement refuted on `r ≥ 1` |
| --- | --- |
| `lemma5_as_registered_is_false` | The bound with `c = 11/100` |
| `paper_lemma5_range_ge_one_is_false` | The bound with `c = 1/8` |

Both declarations are available from the root module, are unconditional, and pass the project's
[axiom audit](lean4/scripts/check_axioms.sh). Their
[proofs](lean4/TSDPP/Lemma5Refutation.lean) combine the containment, closed-form Beta tails,
and rational bounds on exponentials.

## Why the bound fails outside the stated range

The counterexample family gives a direct comparison. For `Beta(1, n)`, the same containment gives

```
LB_n(r) = (1 − (r+1)/(n+1))^n · (1 − (n/(n+1))^n),  1 ≤ r < n.
```

For each fixed `r`, as `n → ∞`, this lower bound tends to
`exp(−(r+1)) · (1 − exp(−1))`. Its exponent is linear in `r`, whereas the claimed bound
`2 exp(−cr²)` has a quadratic exponent. For sufficiently large fixed `r`, the limiting lower
bound exceeds the claimed upper bound, and so does `LB_n(r)` for sufficiently large `n`.
This explains the failure of the unrestricted extension; the finite witness above supplies the
machine-checked instance.

## What the artifact establishes

Refuting a bound used in a proof does not, by itself, refute the theorem. A regret counterexample
would require the underlying problem and policy, which this artifact does not formalize.

In `theorem2_concrete`, `BR` and `J` are abstract reals subject to hypotheses. The resulting
regret-rate statement is conditional on those hypotheses, including the decomposition and
concentration premises. Connecting it to the paper's constrained policy remains unestablished.
[FIDELITY.md](FIDELITY.md) audits this boundary.

## Additional gaps in the formalized analysis

[DESIGN.md](DESIGN.md) §5 and §7 record six further deviations and their scope.
Eq. (40) is a distinct case: its final printed inequality is false, as documented in
[FIDELITY.md §3.1](FIDELITY.md), but the discrepancy
is a constant factor and does not change the asymptotic dependence on `T`.
`scripts/numeric_check.py` does not test this step.
