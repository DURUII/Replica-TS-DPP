#!/usr/bin/env python
"""Second, structurally different reduction for the same probability:

   (R1)  P(|X-Y| >= t) = 2 int_0^{1-t} f(y) (1 - F(y+t)) dy      [upper tail]
   (R3)  P(|X-Y| >= t) = 2 int_t^1     f(x) F(x-t)     dy      [lower tail, integrate x]

R1 and R3 are the same number by Fubini (integrate the region y <= x-t in the two
orders).  Numerically they use *different* tails and *different* branches of the
continued fraction, so they are not the same code path.
"""
import numpy as np
import sys
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from scipy.integrate import quad
from scipy.special import gammaln
from recon_l5_fast import betacf, logtail, log_LHS

def logIbeta_f(a, b, x):
    """log I_x(a,b) (x below the mean only, where it is accurate)."""
    lb = gammaln(a) + gammaln(b) - gammaln(a + b)
    return -lb + a * np.log(x) + b * np.log1p(-x) + np.log(betacf(a, b, x)) - np.log(a)

def g3(x, a, b, t):
    """log of f(x)*F(x-t) for x in (t,1)."""
    if x <= t or x >= 1:
        return -np.inf
    lb = gammaln(a) + gammaln(b) - gammaln(a + b)
    lp = (a - 1) * np.log(x) + (b - 1) * np.log1p(-x) - lb
    z = x - t
    lF = logIbeta_f(a, b, z) if z > 0 else -np.inf
    return lp + lF

def log_LHS_R3(a, b, t):
    if t >= 1:
        return -np.inf, {}
    # peak of g3 : scan in the variable w = x - t (same rescaling logic)
    ws = np.unique(np.concatenate([np.logspace(-13, np.log10(max(1 - t, 1e-12) * .5), 600),
                                   np.linspace(1e-12, 1 - t - 1e-12, 900)]))
    xs = t + ws
    vals = np.array([g3(x, a, b, t) for x in xs])
    vals = vals[np.isfinite(vals)] if np.isfinite(vals).any() else vals
    i = int(np.argmax(vals))
    m = vals[i]
    if not np.isfinite(m):
        return -np.inf, {}
    xp = xs[i]
    def scaled(x):
        v = g3(x, a, b, t)
        return np.exp(v - m) if np.isfinite(v) else 0.0
    v, e = quad(scaled, t, 1.0, limit=400, points=[xp] if t < xp < 1 else None,
                epsabs=1e-14, epsrel=1e-13)
    return m + np.log(v) + np.log(2), {'val': v, 'abserr': e}

CASES = [(1, 100, 10), (2, 200, 10), (5, 500, 10), (10, 1000, 10), (25, 2500, 10),
         (50, 5000, 10), (500, 50000, 10), (5000, 500000, 10),
         (5000, 500000, 5), (500, 50000, 7), (2, 40, 10), (5, 500, 5)]

print(f"{'a':>6}{'b':>9}{'r':>4} {'log LHS (R1)':>16} {'log LHS (R3)':>16} {'dlog':>10} "
      f"{'LHS':>13} {'c_eff':>9} {'c_eff(R3)':>10}")
for (a, b, r) in CASES:
    t = r / (1 + b / a)
    if t >= 1:
        print(f"{a:>6}{b:>9}{r:>4}   t={t:.4f} >= 1 : EMPTY EVENT (LHS=0)")
        continue
    lg1, i1 = log_LHS(a, b, t)
    lg3, i3 = log_LHS_R3(a, b, t)
    c1 = -(lg1 - np.log(2)) / (a * r * r)
    c3 = -(lg3 - np.log(2)) / (a * r * r)
    print(f"{a:>6}{b:>9}{r:>4} {lg1:>16.6f} {lg3:>16.6f} {lg1-lg3:>10.2e} "
          f"{np.exp(lg1) if lg1>-740 else 0.0:>13.5e} {c1:>9.5f} {c3:>10.5f}")

print()
print("RHS comparison for the violating cells:")
for (a, b, r) in [(1, 100, 10), (2, 200, 10), (5, 500, 10), (10, 1000, 10),
                  (50, 5000, 10), (500, 50000, 10), (5000, 500000, 10),
                  (5000, 500000, 5), (500, 50000, 7)]:
    t = r / (1 + b / a)
    lg1, _ = log_LHS(a, b, t)
    lhs = np.exp(lg1) if lg1 > -740 else 0.0
    rhs11 = 2 * np.exp(-0.11 * a * r * r)
    rhs125 = 2 * np.exp(-0.125 * a * r * r)
    lr11 = np.exp(lg1 - np.log(rhs11)); lr125 = np.exp(lg1 - np.log(rhs125))
    print(f"  a={a:<6} b={b:<8} r={r:<3} LHS/RHS(.11)={lr11:.4g}  LHS/RHS(1/8)={lr125:.4g}"
          f"   {'VIOLATES 11/100' if lr11>1 else ''} {'VIOLATES 1/8' if lr125>1 else ''}")
