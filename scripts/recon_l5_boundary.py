#!/usr/bin/env python
"""1) where exactly does the bound fail?  finer r-grid at large rho / large alpha
2) is the bound safe on the paper's OWN stated range 0 <= r <= 1?
3) independent mpmath re-check of the largest-alpha cells."""
import sys
import numpy as np
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from recon_l5_fast import log_LHS

def ceff(a, rho, r):
    t = r / (1 + rho)
    if t >= 1:
        return None
    lg, info = log_LHS(a, a * rho, t)
    return -(lg - np.log(2)) / (a * r * r), lg, info

print("=== 1. r-boundary of the violation, rho in {20,50,100}, r in 1..12 ===")
print("(c_eff;  bold flag when < 0.11 or < 0.125)")
for rho in [10, 20, 50, 100]:
    for a in [1, 2, 5, 10, 50, 500, 5000]:
        row = []
        for r in [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12]:
            o = ceff(a, rho, r)
            if o is None:
                row.append("    --   ")
            else:
                c = o[0]
                mark = "*" if c < 0.11 else ("+" if c < 0.125 else " ")
                row.append(f"{c:8.4f}{mark}")
        print(f"  rho={rho:<4} a={a:<5} " + "".join(row))
    print()
print("  (* = c_eff < 0.11 : violates the artifact's constant;"
      " + = 0.11 <= c_eff < 0.125 : violates the paper's 1/8 only)")

print()
print("=== 2. the paper's own stated range 0 <= r <= 1 ===")
print("    (min c_eff over r in (0,1], and whether any cell violates c=1/8)")
worst = (1e9, None)
for a in [0.5, 1, 2, 5, 10, 25, 50, 100, 500, 5000]:
    for rho in [0.05, 0.1, 0.25, 0.5, 1, 2, 5, 10, 50, 100]:
        for r in [0.05, 0.1, 0.25, 0.5, 0.75, 0.9, 1.0]:
            o = ceff(a, rho, r)
            if o is None:
                continue
            c = o[0]
            if c < worst[0]:
                worst = (c, (a, rho, r))
print(f"    min c_eff over the whole r<=1 sub-grid: {worst[0]:.5f} at (a,rho,r)={worst[1]}")
print(f"    -> both 0.11 and 1/8 are safe on the paper's printed range" if worst[0] > 0.125
      else "    -> VIOLATION inside r<=1")
