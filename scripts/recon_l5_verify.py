#!/usr/bin/env python
"""Independent high-precision evaluation of Pr(|X-Y| >= t) for Beta(a,b) i.i.d.,
and the first hard test of the paper's Lemma 5 (r >= 1 form)."""
import sys
import numpy as np
import mpmath as mp
from scipy.integrate import quad
from scipy.special import betainc, betaln
from scipy.optimize import minimize_scalar
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from recon_l5_mp import log_tail, betacf

# ---------------------------------------------------------------- double helpers
def gd(y, a, b, t):
    """log integrand in double, with a floor on the tail."""
    if y <= 0 or y >= 1 - t:
        return -np.inf
    lp = (a - 1) * np.log(y) + (b - 1) * np.log1p(-y) - betaln(a, b)
    tail = 1.0 - betainc(a, b, min(y + t, 1.0))
    lt = np.log(tail) if tail > 1e-300 else -700.0
    return lp + lt

def find_peak(a, b, t):
    hi = 1 - t
    # log-spaced near 0 + uniform: catches both the singular corner and the bulk
    grid = np.unique(np.concatenate([
        np.logspace(-14, np.log10(hi / 2), 700),
        np.linspace(hi * 1e-9, hi * (1 - 1e-12), 1400)]))
    vals = np.array([gd(y, a, b, t) for y in grid])
    i = int(np.argmax(vals))
    lo = grid[max(i - 1, 0)]
    up = grid[min(i + 1, len(grid) - 1)]
    if not np.isfinite(vals[i]):
        return None
    if i == 0 or i == len(grid) - 1:
        return grid[i]
    res = minimize_scalar(lambda y: -gd(y, a, b, t), bounds=(lo, up), method='bounded')
    cands = [(grid[i], vals[i]), (res.x, -res.fun)]
    y, _ = max(cands, key=lambda p: p[1])
    return float(y)

def lhs_double(a, b, t):
    """scipy R1, returns (value, quad_err, nwarn)"""
    def f(y):
        if y <= 0 or y >= 1 - t:
            return 0.0
        lp = (a - 1) * np.log(y) + (b - 1) * np.log1p(-y) - betaln(a, b)
        return np.exp(lp) * (1.0 - betainc(a, b, min(y + t, 1.0)))
    pts = []
    yp = find_peak(a, b, t)
    if yp is not None and 0 < yp < 1 - t:
        pts.append(yp)
    import warnings
    with warnings.catch_warnings(record=True) as w:
        warnings.simplefilter("always")
        v, e = quad(f, 0.0, 1 - t, limit=500, points=pts or None,
                    epsabs=1e-300, epsrel=1e-14)
        nw = len(w)
    return 2 * v, 2 * e, nw, (pts[0] if pts else None)

# ---------------------------------------------------------------- mpmath path
def lhs_mp(a, b, t, dps=60, ypeak=None):
    """R1 in mpmath.  Real value can be e^{-40000}; everything in log space."""
    mp.mp.dps = dps
    A, B, T = mp.mpf(a), mp.mpf(b), mp.mpf(t)
    lbeta = mp.loggamma(A) + mp.loggamma(B) - mp.loggamma(A + B)

    def gfun(y):
        if y <= 0 or y >= 1 - T:
            return mp.mpf('-inf')
        return ((A - 1) * mp.log(y) + (B - 1) * mp.log1p(-y) - lbeta
                + log_tail(A, B, y + T))

    knots = [mp.mpf(0)]
    if ypeak is not None and 0 < ypeak < 1 - T:
        knots.append(mp.mpf(ypeak))
    knots.append(1 - T)
    # integrate exp(g) piecewise; mpmath handles huge negative exponents
    return 2 * mp.quad(lambda y: mp.e ** gfun(y), knots)

def lhs_mp_R2(a, b, t, dps=60):
    """Independent reduction: P = 1 - int f(y)[clamp(F(y+t)) - clamp(F(y-t))]dy."""
    mp.mp.dps = dps
    A, B, T = mp.mpf(a), mp.mpf(b), mp.mpf(t)
    lbeta = mp.loggamma(A) + mp.loggamma(B) - mp.loggamma(A + B)
    L = mp.mpf
    def F(z):
        z = min(max(z, L(0)), L(1))
        if z <= 0:
            return L(0)
        if z >= 1:
            return L(1)
        from recon_l5_mp import logIbeta
        return mp.e ** logIbeta(A, B, z)
    def integ(y):
        if y <= 0 or y >= 1:
            return L(0)
        lp = (A - 1) * mp.log(y) + (B - 1) * mp.log1p(-y) - lbeta
        return mp.e ** lp * (F(y + T) - F(y - T))
    # split at the kinks y = t and y = 1-t
    knots = [L(0), L(min(T, L(1))), L(max(L(0), 1 - T)), L(1)]
    knots = sorted(set(knots))
    return 1 - mp.quad(integ, knots)

if __name__ == "__main__":
    mp.mp.dps = 60
    print("=== A. uniform a=b=1 : exact (1-t)^2, both reductions ===")
    for t in [0.5, 0.2, 0.01]:
        v1 = lhs_mp(1, 1, t)
        v2 = lhs_mp_R2(1, 1, t)
        print(f"  t={t:<5} R1={mp.nstr(v1,20)}  R2={mp.nstr(v2,20)}  exact={(1-t)**2:.20f}")

    print()
    print("=== B. mpmath R1 vs scipy R1 vs reduction R2 ===")
    for (a, b, t) in [(2, 2, 0.5), (2, 2, 0.25), (0.5, 0.5, 0.5), (3, 7, 0.4),
                      (1, 4, 0.3), (50, 50, 0.5), (2, 200, 0.09900990099009901),
                      (5, 500, 0.09900990099009901)]:
        yp = find_peak(a, b, t)
        v1 = lhs_mp(a, b, t, ypeak=yp)
        v2 = lhs_mp_R2(a, b, t)
        vd, ed, nw, _ = lhs_double(a, b, t)
        rel = abs(v1 - v2) / v2 if v2 != 0 else mp.mpf('nan')
        print(f"  a={a:<5} b={b:<6} t={t:.6f}  R1={mp.nstr(v1,12)}  R2={mp.nstr(v2,12)} "
              f" rel(R1,R2)={mp.nstr(rel,3)}   scipy={vd:.10e} (err {ed:.1e} warn {nw})")
