#!/usr/bin/env python
"""High-precision tooling for Pr(|X-Y| >= t), X,Y ~ Beta(a,b) i.i.d.

Uses mpmath at 60 dps with a Numerical-Recipes-style continued fraction for the
regularized incomplete beta (scipy's betainc is fine in double, mpmath's own
betainc fails for large shapes, so we implement it).

Two *independent* reductions of the same probability are computed:
  (R1)  P(|X-Y| >= t) = 2 * int_0^{1-t} f(y) (1 - I_{y+t}(a,b)) dy      [one-sided x2]
  (R2)  P(|X-Y| >= t) = 1 - int_0^1 f(y) [F(y+t) - F(y-t)]_clamped dy  [complement]
R1 == R2 is an exact identity; agreement is a check on the code, not on the maths.
"""
import mpmath as mp

def betacf(a, b, x, maxit=20000, eps=None):
    """Continued fraction for the incomplete beta (Lentz).  x in [0,1]."""
    if eps is None:
        eps = mp.mpf(10) ** (-(mp.mp.dps - 8))
    FPMIN = mp.mpf(10) ** (-(mp.mp.dps + 10))
    qab, qap, qam = a + b, a + 1, a - 1
    c = mp.mpf(1)
    d = 1 - qab * x / qap
    if abs(d) < FPMIN:
        d = FPMIN
    d = 1 / d
    h = d
    for m in range(1, maxit):
        m2 = 2 * m
        aa = m * (b - m) * x / ((qam + m2) * (a + m2))
        d = 1 + aa * d
        if abs(d) < FPMIN:
            d = FPMIN
        c = 1 + aa / c
        if abs(c) < FPMIN:
            c = FPMIN
        d = 1 / d
        h *= d * c
        aa = -(a + m) * (qab + m) * x / ((a + m2) * (qap + m2))
        d = 1 + aa * d
        if abs(d) < FPMIN:
            d = FPMIN
        c = 1 + aa / c
        if abs(c) < FPMIN:
            c = FPMIN
        d = 1 / d
        de = d * c
        h *= de
        if abs(de - 1) < eps:
            break
    else:
        raise RuntimeError(f"betacf: no convergence a={a} b={b} x={x}")
    return h

def logIbeta(a, b, x):
    """log of the regularized incomplete beta I_x(a,b), valid for tiny values."""
    if x <= 0:
        return mp.mpf('-inf')
    if x >= 1:
        return mp.mpf(0)
    # 1 - I_x(a,b) = I_{1-x}(b,a) = bt * betacf(b,a,1-x) / b,  with
    # bt = exp(lgamma(a+b) - lgamma(a) - lgamma(b) + a log x + b log(1-x))
    # Use it for the *tail*; for I itself use the symmetric split (NR).
    if x < (a + 1) / (a + b + 2):
        lb = mp.loggamma(a) + mp.loggamma(b) - mp.loggamma(a + b)
        return (-lb + a * mp.log(x) + b * mp.log1p(-x)
                + mp.log(betacf(a, b, x)) - mp.log(a))
    else:
        return mp.log(1 - mp.e ** log_tail(a, b, x))

def log_tail(a, b, x):
    """log(1 - I_x(a,b))"""
    if x >= 1:
        return mp.mpf('-inf')
    if x <= 0:
        return mp.mpf(0)
    # The CF for I converges only for x < (a+1)/(a+b+2); above that use
    # 1 - I_x(a,b) = I_{1-x}(b,a) = bt * betacf(b,a,1-x)/b  (same bt as above)
    lb = mp.loggamma(a) + mp.loggamma(b) - mp.loggamma(a + b)
    if x >= (a + 1) / (a + b + 2):
        return (-lb + a * mp.log(x) + b * mp.log1p(-x)
                + mp.log(betacf(b, a, 1 - x)) - mp.log(b))
    logI = (-lb + a * mp.log(x) + b * mp.log1p(-x)
            + mp.log(betacf(a, b, x)) - mp.log(a))
    return mp.log1p(-mp.e ** logI)
