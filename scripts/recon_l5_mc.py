#!/usr/bin/env python
"""Independent confirmation of the candidate counterexamples:
 (i)   Monte Carlo (numpy), 2e8 samples
 (ii)  direct 2-D quadrature of the joint density over the region |x-y|>=t
 (iii) closed form for integer shapes via the incomplete-beta series
"""
import numpy as np
from scipy.integrate import dblquad, quad
from scipy.special import betainc, beta as betafn, betaln
from scipy.stats import beta as bdist
import sys
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from recon_l5_verify import lhs_double, find_peak
import mpmath as mp
from recon_l5_mp import log_tail

def lhs_double_full(a, b, t):
    def f(y):
        if y <= 0 or y >= 1 - t:
            return 0.0
        lp = (a - 1) * np.log(y) + (b - 1) * np.log1p(-y) - betaln(a, b)
        return np.exp(lp) * (1.0 - betainc(a, b, min(y + t, 1.0)))
    yp = find_peak(a, b, t)
    pts = [yp] if (yp is not None and 0 < yp < 1 - t) else None
    v, e = quad(f, 0.0, 1 - t, limit=600, points=pts, epsabs=1e-300, epsrel=1e-14)
    return 2 * v, 2 * e

def mc(a, b, t, n, seed=12345):
    rng = np.random.default_rng(seed)
    hit = 0
    B = 20_000_000
    done = 0
    while done < n:
        k = min(B, n - done)
        x = rng.beta(a, b, k)
        y = rng.beta(a, b, k)
        hit += int(np.count_nonzero(np.abs(x - y) >= t))
        done += k
    p = hit / n
    se = np.sqrt(max(p * (1 - p), 1e-30) / n)
    return hit, n, p, se

def dblquad_lhs(a, b, t):
    """int int over |x-y|>=t of the joint density, straight 2-D quadrature."""
    def inner(x, y):
        if abs(x - y) < t:
            return 0.0
        return np.exp((a - 1) * np.log(x) + (b - 1) * np.log1p(-x) - betaln(a, b)
                      + (a - 1) * np.log(y) + (b - 1) * np.log1p(-y) - betaln(a, b))
    v, e = dblquad(inner, 0, 1, 0, 1, epsabs=1e-14, epsrel=1e-10)
    return v, e

CASES = [(2, 200, 10), (1, 100, 10), (5, 500, 10), (2, 20, 5), (1, 20, 5), (1, 10, 3)]

print("case-by-case: candidate counterexamples")
print(f"{'a':>5}{'b':>7}{'r':>4}{'t':>10}   {'exact LHS (mp, 60dps)':>26} {'RHS c=.11':>12} {'RHS c=1/8':>12} {'L/R(.11)':>10} {'c_eff':>9}")
for (a, b, r) in CASES:
    rho = b / a
    t = r / (1 + rho)
    if t >= 1:
        print(f"{a:>5}{b:>7}{r:>4}{t:>10.6f}   EMPTY EVENT")
        continue
    mp.mp.dps = 60
    A, Bnd, T = mp.mpf(a), mp.mpf(b), mp.mpf(t)
    yp = find_peak(a, b, t)
    lbeta = mp.loggamma(A) + mp.loggamma(Bnd) - mp.loggamma(A + Bnd)
    def gf(y):
        if y <= 0 or y >= 1 - T:
            return mp.mpf('-inf')
        return (A - 1) * mp.log(y) + (Bnd - 1) * mp.log1p(-y) - lbeta + log_tail(A, Bnd, y + T)
    knots = [mp.mpf(0)] + ([mp.mpf(yp)] if (yp and 0 < yp < 1 - T) else []) + [1 - T]
    L = 2 * mp.quad(lambda y: mp.e ** gf(y), knots)
    rhs1 = 2 * np.exp(-0.11 * a * r * r)
    rhs2 = 2 * np.exp(-0.125 * a * r * r)
    ceff = -float(mp.log(L / 2)) / (a * r * r)
    print(f"{a:>5}{b:>7}{r:>4}{t:>10.6f}   {mp.nstr(L,10):>26} {rhs1:>12.4e} {rhs2:>12.4e} {float(L)/rhs1:>10.3f} {ceff:>9.5f}")

print()
print("3-way confirmation on the smallest-alpha counterexample (1,100,10), t=10/101")
a, b, r = 1, 100, 10
t = r / (1 + b / a)
print(f"  t = {t!r} = {t:.12f}")
L_d, L_e = lhs_double_full(a, b, t)
print(f"  scipy 1-D reduction : {L_d:.12e}  (quad abserr {L_e:.1e})")
mp.mp.dps = 50
# closed form for a=1: LHS = 2*int_t^1 b*u^(b-1)*(u-t)^b du
bb = mp.mpf(100); tt = mp.mpf(10) / 101
v = 2 * bb * mp.quad(lambda u: u ** (bb - 1) * (u - tt) ** bb, [tt, 1])
print(f"  closed form (a=1)   : {mp.nstr(v,12)}")
A, Bnd = mp.mpf(1), mp.mpf(100)
LB = mp.loggamma(A) + mp.loggamma(Bnd) - mp.loggamma(A + Bnd)
def gf(y):
    if y <= 0 or y >= 1 - tt:
        return mp.mpf('-inf')
    return (A - 1) * mp.log(y) + (Bnd - 1) * mp.log1p(-y) - LB + log_tail(A, Bnd, y + tt)
print(f"  mpmath 1-D reduction: {mp.nstr(2*mp.quad(lambda y: mp.e**gf(y), [mp.mpf(0), mp.mpf(1)-tt]), 12)}")
try:
    v2, e2 = dblquad_lhs(2, 200, 10 / 101)
    print(f"  direct 2-D dblquad, (2,200,10): {v2:.6e}  (est err {e2:.1e})")
except Exception as ex:
    print(f"  direct 2-D dblquad failed: {ex}")
print("  RHS at c=0.11 :", 2 * np.exp(-0.11 * a * r * r))
print("  RHS at c=1/8  :", 2 * np.exp(-0.125 * a * r * r))

print()
print("Monte Carlo, 2e8 samples each:")
for (a, b, r) in [(1, 100, 10), (1, 20, 5), (2, 20, 5)]:
    t = r / (1 + b / a)
    hit, n, p, se = mc(a, b, t, 200_000_000)
    rhs1 = 2 * np.exp(-0.11 * a * r * r)
    print(f"  a={a} b={b} r={r} t={t:.6f}: hits={hit}/{n}  p={p:.6e} +- {se:.1e}   "
          f"RHS(.11)={rhs1:.4e}   p/RHS={p/rhs1:.3f}")
