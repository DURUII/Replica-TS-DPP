#!/usr/bin/env python
"""Leading large-alpha exponent of Pr(|X-Y| >= r*mu), mu = alpha/(alpha+beta).

Derivation attempt (exploratory, double precision):
  log f(y)      ~ -alpha * G(y),   G(y) = log(mu/y) + rho*log((1-mu)/(1-y))
  log(1-F(z))   ~ -alpha * G(z)    (Laplace on the same density, z > mu)
  Pr(X-Y>=t) = int_0^{1-t} f(y)(1-F(y+t)) dy   (exact reduction, times 2 by symmetry)
  => -log Pr ~ alpha * min_{y in (0,1-t)} [G(y) + G(y+t)]  =: alpha * Lam(rho,r)
  => c_eff := -log(LHS/2)/(alpha r^2) -> Lam/r^2 for alpha -> infinity.

Rescale u = y/mu:  u in (0, 1+rho-r), t = r*mu, mu = 1/(1+rho).
  F(u) = -log u - log(u+r) + rho*log(rho) - rho*log(1+rho)
               - rho*log(1-mu*u) - rho*log(1-mu*(u+r))
and Lam = min_u F(u).
"""
import numpy as np
from scipy.optimize import minimize_scalar

def F_of_u(u, r, rho):
    mu = 1.0 / (1.0 + rho)
    if u <= 0 or u >= 1.0 / mu:
        return np.inf
    if 1 - mu * u <= 0 or 1 - mu * (u + r) <= 0:
        return np.inf
    return (-np.log(u) - np.log(u + r)
            + rho * np.log(rho) - rho * np.log(1 + rho)
            - rho * np.log1p(-mu * u) - rho * np.log1p(-mu * (u + r)))

def Lam(rho, r):
    """min over the whole admissible u-range (0, 1+rho-r)."""
    umax = 1.0 + rho - r
    if umax <= 0:
        return None
    lo, hi = 1e-14 * umax, umax * (1 - 1e-14)
    res = minimize_scalar(F_of_u, args=(r, rho), bounds=(lo, hi), method='bounded',
                          options={'xatol': 1e-14})
    us = np.linspace(lo, hi, 200001)
    vals = [F_of_u(u, r, rho) for u in us]
    i = int(np.argmin(vals))
    if vals[i] < res.fun:
        return vals[i], us[i]
    return res.fun, res.x

if __name__ == "__main__":
    print("c_pred = Lam/r^2   (predicted large-alpha c_eff;  violation of c=0.11 if < 0.11)")
    print("      " + "".join(f"{r:>9}" for r in [1, 1.05, 1.1, 1.25, 1.5, 2, 3, 5, 10]))
    print("  rho " + "".join(f"{'r='+str(r):>9}" for r in [1, 1.05, 1.1, 1.25, 1.5, 2, 3, 5, 10]))
    for rho in [0.05, 0.1, 0.25, 0.5, 1, 2, 5, 10, 50, 100]:
        row = []
        for r in [1, 1.05, 1.1, 1.25, 1.5, 2, 3, 5, 10]:
            if r > 1 + rho:
                row.append("   --   ")   # t > 1: event empty
                continue
            out = Lam(rho, r)
            if out is None:
                row.append("   --   ")
            else:
                lam, u = out
                row.append(f"{lam/r**2:9.4f}")
        print(f"{rho:5} " + "".join(row))
    print()
    print("r=10 slices (the suspicious corner): same table but c_pred")
    for rho in [9.5, 10, 12, 20, 50, 100, 1000, 10**4, 10**6]:
        out = Lam(rho, 10)
        if out:
            print(f"   rho={rho:<9} c_pred={out[0]/100:.6f}   u*={out[1]:.6f}")
