#!/usr/bin/env python
"""Fast, underflow-free evaluation of LHS = Pr(|X-Y| >= t), X,Y ~ Beta(a,b) iid.

Idea: never form the density or the tail as plain floats.  Work with
    g(y) = log f(y) + log(1 - F(y+t))        (all in log space)
    m    = max_y g(y)
    I    = e^m * int_0^{1-t} exp(g(y) - m) dy
The scaled integrand exp(g-m) lies in (0,1] so nothing underflows, and the
final log of the answer is m + log(int).  Absolute error in g is ~1e-9 worst
case (cancellation in lgamma terms of size ~1e6), which is negligible for the
exponent: c_eff = -(m + log(int) + log 2)/(a r^2).

log(1 - I_x(a,b)) is computed with the NR continued fraction in float, so the
tiny tail never has to be materialised.
"""
import numpy as np
from scipy.integrate import quad
from scipy.special import gammaln

def betacf(a, b, x, maxit=200000, eps=1e-15):
    FPMIN = 1e-300
    qab, qap, qam = a + b, a + 1, a - 1
    c = 1.0
    d = 1.0 - qab * x / qap
    if abs(d) < FPMIN:
        d = FPMIN
    d = 1.0 / d
    h = d
    for m in range(1, maxit):
        m2 = 2 * m
        aa = m * (b - m) * x / ((qam + m2) * (a + m2))
        d = 1.0 + aa * d
        if abs(d) < FPMIN:
            d = FPMIN
        c = 1.0 + aa / c
        if abs(c) < FPMIN:
            c = FPMIN
        d = 1.0 / d
        h *= d * c
        aa = -(a + m) * (qab + m) * x / ((a + m2) * (qap + m2))
        d = 1.0 + aa * d
        if abs(d) < FPMIN:
            d = FPMIN
        c = 1.0 + aa / c
        if abs(c) < FPMIN:
            c = FPMIN
        d = 1.0 / d
        de = d * c
        h *= de
        if abs(de - 1.0) < eps:
            break
    else:
        raise RuntimeError(f"betacf no convergence a={a} b={b} x={x}")
    return h

_LG = np.vectorize(gammaln, otypes=[float])

def logtail(a, b, x):
    """log(1 - I_x(a,b)).  Two branches: the CF for I converges only for
    x < (a+1)/(a+b+2), so above that point we use the *complement* identity
    1 - I_x(a,b) = I_{1-x}(b,a) (whose own CF argument 1-x is then small)."""
    if x >= 1.0:
        return -np.inf
    if x <= 0.0:
        return 0.0
    lb = gammaln(a) + gammaln(b) - gammaln(a + b)
    if x >= (a + 1.0) / (a + b + 2.0):
        return (-lb + a * np.log(x) + b * np.log1p(-x)
                + np.log(betacf(b, a, 1.0 - x)) - np.log(b))
    logI = (-lb + a * np.log(x) + b * np.log1p(-x)
            + np.log(betacf(a, b, x)) - np.log(a))
    return np.log1p(-np.exp(logI))

def gfun(y, a, b, t):
    if y <= 0 or y >= 1 - t:
        return -np.inf
    return ((a - 1) * np.log(y) + (b - 1) * np.log1p(-y)
            - (gammaln(a) + gammaln(b) - gammaln(a + b))
            + logtail(a, b, y + t))

def _peak(a, b, t):
    hi = 1.0 - t
    grid = np.unique(np.concatenate([
        np.logspace(-13, np.log10(hi * 0.5), 600),
        np.linspace(hi * 1e-9, hi * (1 - 1e-12), 800)]))
    vals = np.array([gfun(y, a, b, t) for y in grid])
    if not np.isfinite(vals).any():
        return None, -np.inf
    i = int(np.argmax(vals))
    if i == 0 or i == len(grid) - 1 or not np.isfinite(vals[i]):
        return float(grid[i]), float(vals[i])
    lo, up = grid[i - 1], grid[i + 1]
    for _ in range(200):     # golden-section on g
        m1 = lo + 0.382 * (up - lo)
        m2 = lo + 0.618 * (up - lo)
        if gfun(m1, a, b, t) > gfun(m2, a, b, t):
            up = m2
        else:
            lo = m1
    y = 0.5 * (lo + up)
    return y, gfun(y, a, b, t)

def log_LHS(a, b, t):
    """returns (log LHS, info dict) with LHS = Pr(|X-Y| >= t)."""
    if t >= 1.0:
        return -np.inf, {'empty': True}
    yp, m = _peak(a, b, t)
    if yp is None:
        return -np.inf, {'empty': True}
    def scaled(y):
        v = gfun(y, a, b, t)
        return np.exp(v - m) if np.isfinite(v) else 0.0
    knots = []
    if 0 < yp < 1 - t:
        knots.append(yp)
    # endpoints of the active range; y<0 or y>1-t gives zero
    v, e = quad(scaled, max(0.0, 0.0), 1 - t, limit=400, points=knots or None,
                epsabs=1e-14, epsrel=1e-13)
    logI = m + np.log(v)                       # I = int_0^{1-t} f(y)(1-F(y+t)) dy
    return logI + np.log(2), {'val': v, 'abserr_scaled': e, 'ypeak': yp, 'm': m}

def LHS(a, b, t):
    lg, info = log_LHS(a, b, t)
    return (np.exp(lg) if lg > -700 else 0.0), lg, info
