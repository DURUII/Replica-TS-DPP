#!/usr/bin/env python
"""Exploratory probe: is the 1-D reduction integrable by scipy quad / mpmath
across the (alpha,beta) range of the sweep?  Nothing here is a proof."""
import numpy as np, mpmath as mp
from scipy.integrate import quad
from scipy.special import betainc, betaln
from scipy.stats import beta as betadist

mp.mp.dps = 50

def lhs_scipy(a, b, t, limit=400, epsabs=1e-14, epsrel=1e-13):
    """Pr(|X-Y| >= t) = 2 * int_0^{1-t} f(y) (1 - I_{y+t}(a,b)) dy."""
    if t >= 1.0:
        return 0.0, 0.0, 0
    def f(y):
        if y <= 0 or y >= 1:
            return 0.0
        # log pdf
        lp = (a - 1) * np.log(y) + (b - 1) * np.log1p(-y) - betaln(a, b)
        return np.exp(lp) * (1.0 - betainc(a, b, min(y + t, 1.0)))
    pts = [0.0]
    # mode of f (for a,b>1) as an extra breakpoint helps concentration
    if a > 1 and b > 1:
        ymax = (a - 1) / (a + b - 2)
        if 0 < ymax < 1 - t:
            pts.append(ymax)
    pts.append(1 - t)
    import warnings
    with warnings.catch_warnings(record=True) as w:
        warnings.simplefilter("always")
        val, err = quad(f, 0.0, 1 - t, limit=limit, points=pts[1:-1] or None,
                        epsabs=epsabs, epsrel=epsrel)
        nw = len([x for x in w if issubclass(x.category, Exception)])
    return 2 * val, 2 * err, nw

def lhs_mp(a, b, t, dps=50):
    """Same integral in mpmath, split at the mode, tanh-sinh."""
    mp.mp.dps = dps
    A, B, T = mp.mpf(a), mp.mpf(b), mp.mpf(t)
    lbeta = mp.betaln(A, B)
    def f(y):
        if y <= 0 or y >= 1:
            return mp.mpf(0)
        lp = (A - 1) * mp.log(y) + (B - 1) * mp.log1p(-y) - lbeta
        return mp.e ** lp * (1 - mp.betainc(A, B, 0, min(y + T, mp.mpf(1)), regularized=True))
    knots = [mp.mpf(0)]
    if a > 1 and b > 1:
        ym = (A - 1) / (A + B - 2)
        if 0 < ym < 1 - T:
            knots.append(ym)
    knots.append(1 - T)
    return 2 * mp.quad(f, knots)

print("=== validation 1: uniform  a=b=1, LHS should be (1-t)^2 ===")
for t in [0.5, 0.2, 0.1, 0.01, 0.99]:
    v, e, nw = lhs_scipy(1, 1, t)
    print(f"t={t:<6} quad={v:.15f} exact={(1-t)**2:.15f} diff={v-(1-t)**2:+.3e} err={e:.2e} warns={nw}")

print()
print("=== probe: quad vs mpmath across shapes ===")
cases = [(2,2,0.5),(0.5,0.5,0.5),(1,4,0.3),(3,7,0.4),(50,50,0.5),(500,500,0.5),
         (0.5,50,0.0099),(10,10,0.5),(5000,500,0.0099),(100,100,0.1),(5000,50000,0.03),
         (0.5,0.5,0.99),(25,250,0.02),(5000,100,0.5)]
for a,b,t in cases:
    v,e,nw = lhs_scipy(a,b,t)
    try:
        vm = lhs_mp(a,b,t)
        rel = abs(mp.mpf(v) - vm)/vm if vm != 0 else mp.mpf('nan')
    except Exception as ex:
        vm, rel = None, f"mpmath failed: {ex}"
    print(f"a={a:<7} b={b:<8} t={t:<8} scipy={v:.6e} (err {e:.1e}, warn {nw})  mp={vm}  rel={rel}")
