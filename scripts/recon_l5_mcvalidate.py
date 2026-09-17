#!/usr/bin/env python
"""Validation item 2: moderate (alpha,beta) against a large Monte Carlo run.
Also prints the counterexample cells at full precision."""
import numpy as np, sys
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from recon_l5_fast import log_LHS
from fractions import Fraction

N = 20_000_000
rng = np.random.default_rng(20260917)

def mc(a, b, t, n=N):
    hit = 0
    B = 10_000_000
    done = 0
    while done < n:
        k = min(B, n - done)
        x = rng.beta(a, b, k)
        y = rng.beta(a, b, k)
        hit += int(np.count_nonzero(np.abs(x - y) >= t))
        done += k
    p = hit / n
    return hit, p, np.sqrt(p * (1 - p) / n)

print(f"Monte Carlo validation, N = {N:,} per row")
print(f"{'a':>5}{'b':>6}{'r':>5}{'t':>10} {'MC p':>14} {'+- 1se':>10} {'exact LHS':>16} {'exact/MC':>10} {'z':>7}")
worst_z = 0.0
for (a, b, r) in [(2, 2, 1), (2, 2, 1.5), (5, 5, 1), (5, 5, 2), (10, 10, 1),
                  (20, 20, 1.5), (2, 20, 1), (5, 20, 2), (10, 50, 3), (3, 7, 1.2),
                  (2, 200, 10), (1, 100, 10), (1, 50, 10)]:
    t = r / (1 + b / a)
    if t >= 1:
        print(f"{a:>5}{b:>6}{r:>5}{t:>10.6f}   t>=1 EMPTY")
        continue
    hit, p, se = mc(a, b, t)
    lg, _ = log_LHS(a, b, t)
    ex = np.exp(lg) if lg > -740 else 0.0
    z = (p - ex) / se if se > 0 else 0.0
    worst_z = max(worst_z, abs(z))
    print(f"{a:>5}{b:>6}{r:>5}{t:>10.6f} {p:>14.8e} {se:>10.2e} {ex:>16.8e} {ex/p:>10.5f} {z:>7.2f}")
print(f"\nmax |z| over the MC block: {worst_z:.2f}  (exact != MC would show up as |z| >> 3)")

print()
print("=== full-precision counterexample data ===")
for (a, b, r) in [(2, 200, 10), (1, 100, 10), (5, 500, 10), (10, 1000, 10),
                  (25, 2500, 10), (50, 5000, 10), (5000, 500000, 10), (5000, 500000, 5),
                  (1, 50, 10), (2, 40, 10), (500, 50000, 7)]:
    t = r / (1 + b / a)
    lg, info = log_LHS(a, b, t)
    c = -(lg - np.log(2)) / (a * r * r)
    rhs11 = 2 * np.exp(-0.11 * a * r * r)
    rhs125 = 2 * np.exp(-0.125 * a * r * r)
    print(f"a={a} b={b} r={r}: t = r*a/(a+b) = {Fraction(r*a, a+b)} = {t!r}")
    print(f"    log(LHS)                    = {lg!r}")
    print(f"    LHS                         = {'exp(' + repr(lg) + ')' if lg < -740 else repr(np.exp(lg))}")
    print(f"    LHS/2                       = exp({lg - np.log(2)!r})")
    print(f"    RHS(c=11/100)               = exp({np.log(rhs11)!r})   ({rhs11:.6e})")
    print(f"    RHS(c=1/8)                  = exp({np.log(rhs125)!r})   ({rhs125:.6e})")
    print(f"    LHS/RHS(11/100)             = exp({lg - np.log(rhs11)!r})")
    print(f"    LHS/RHS(1/8)                = exp({lg - np.log(rhs125)!r})")
    print(f"    c_eff                       = {c!r}")
    print(f"    quad relerr on the scaled integrand = {info['abserr_scaled']/info['val']:.2e}")
