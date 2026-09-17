#!/usr/bin/env python
"""THE SWEEP.

Inequality tested, symbol for symbol:

    Pr( |X - Y| >= r * a/(a+b) )  <=  2 * exp( -c * a * r^2 ),      X,Y ~ Beta(a,b) iid
                                                    (a := alpha, b := beta, rho := b/a, t := r/(1+rho))

  * paper (verbatim, p.9 Lemma 5): c = 1/8 = 0.125, stated for 0 <= r <= 1
  * artifact (BetaConcentration.lean): c = 11/100, statement is `1 <= r`

Reported per cell: LHS, RHS at c=0.11, RHS at c=1/8, and
    c_eff := -log(LHS/2)/(a r^2)
which is EXACTLY the largest c for which the inequality holds at that cell
(holds  <=>  c <= c_eff).  So
    c_eff < 0.11   <=> violation at c = 11/100
    c_eff < 0.125  <=> violation at c = 1/8.
Cells with t >= 1 have an empty event (LHS = 0); reported as '--'.
"""
import sys, json, time
import numpy as np
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from recon_l5_fast import log_LHS

ALPHAS = [0.5, 1, 2, 5, 10, 25, 50, 100, 500, 5000]
RHOS = [0.05, 0.1, 0.25, 0.5, 1, 2, 5, 10, 50, 100]
RS = [1, 1.05, 1.1, 1.25, 1.5, 2, 3, 5, 10]

def cell(a, rho, r):
    t = r / (1 + rho)
    if t >= 1:
        return None
    b = a * rho
    logLHS, info = log_LHS(a, b, t)      # log( LHS ), LHS = Pr(|X-Y| >= t)
    if logLHS == -np.inf:
        return dict(lhs=0.0, ceff=np.inf, qerr=0.0, empty=True)
    lhs = np.exp(logLHS)
    # c_eff is defined by  LHS <= 2 e^{-c a r^2}  <=>  c <= -log(LHS/2)/(a r^2)
    ceff = -(logLHS - np.log(2)) / (a * r * r)
    return dict(lhs=lhs, ceff=ceff, qerr=info['abserr_scaled'] / info['val'],
                empty=False, ypeak=info['ypeak'])

def main():
    out = []
    worst_qerr = 0.0
    t0 = time.time()
    for a in ALPHAS:
        for rho in RHOS:
            for r in RS:
                res = cell(a, rho, r)
                if res is None:
                    continue
                rhs11 = 2 * np.exp(-0.11 * a * r * r)
                rhs125 = 2 * np.exp(-0.125 * a * r * r)
                rec = dict(a=a, rho=rho, r=r, t=r / (1 + rho),
                           lhs=res['lhs'], ceff=res['ceff'],
                           rhs11=rhs11, rhs125=rhs125,
                           viol11=bool(res['lhs'] > rhs11),
                           viol125=bool(res['lhs'] > rhs125),
                           qerr=res['qerr'])
                out.append(rec)
                if not res['empty']:
                    # qerr is the relative error of the *scaled* integral, which
                    # equals the absolute error in log(LHS)
                    worst_qerr = max(worst_qerr, res['qerr'])
    print(f"# cells: {len(out)}   wall time {time.time()-t0:.1f}s")
    print(f"# worst scaled-quadrature relative error over the sweep: {worst_qerr:.2e}")
    v11 = [o for o in out if o['viol11']]
    v125 = [o for o in out if o['viol125']]
    print(f"# cells violating c=11/100 : {len(v11)}")
    print(f"# cells violating c=1/8    : {len(v125)}")
    finite = [o for o in out if np.isfinite(o['ceff'])]
    mn = min(finite, key=lambda o: o['ceff'])
    print(f"# infimum of c_eff: {mn['ceff']:.6f} at (a,rho,r) = ({mn['a']},{mn['rho']},{mn['r']}), t={mn['t']:.6f}")
    print()
    print("## violating cells (c = 11/100), sorted by c_eff:")
    for o in sorted(v11, key=lambda o: o['ceff']):
        print(f"   a={o['a']:<6} rho={o['rho']:<5} r={o['r']:<5} t={o['t']:.6f}  LHS={o['lhs']:.6e} "
              f"RHS(.11)={o['rhs11']:.4e} LHS/RHS={o['lhs']/o['rhs11']:.3e}  c_eff={o['ceff']:.5f}")
    print()
    print("## violating cells (c = 1/8) that do NOT violate 11/100:")
    for o in sorted(v125, key=lambda o: o['ceff']):
        if not o['viol11']:
            print(f"   a={o['a']:<6} rho={o['rho']:<5} r={o['r']:<5} t={o['t']:.6f}  LHS={o['lhs']:.6e} "
                  f"RHS(1/8)={o['rhs125']:.4e} LHS/RHS={o['lhs']/o['rhs125']:.3e}  c_eff={o['ceff']:.5f}")
    print()
    print("## 20 smallest c_eff over the whole sweep:")
    for o in sorted(finite, key=lambda o: o['ceff'])[:20]:
        print(f"   a={o['a']:<6} rho={o['rho']:<5} r={o['r']:<5} t={o['t']:.6f}  c_eff={o['ceff']:.5f}  LHS={o['lhs']:.4e}")
    json.dump(out, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'recon_l5_sweep.json'), 'w'))
    print("\n# full table -> scripts/recon_l5_sweep.json")

    # full human-readable table, one block per (alpha,rho)
    print()
    print("## FULL TABLE  (LHS | RHS.11 | RHS.125 | c_eff)   '--' = t>=1, event empty")
    for a in ALPHAS:
        for rho in RHOS:
            rows = [o for o in out if o['a'] == a and o['rho'] == rho]
            if not rows:
                continue
            print(f"-- alpha={a} rho={rho} beta={a*rho} (mu={1/(1+rho):.6g})")
            for o in rows:
                flag = ""
                if o['viol11']:
                    flag += "  <== VIOLATES 11/100"
                if o['viol125']:
                    flag += "  <== VIOLATES 1/8"
                print(f"   r={o['r']:<5} t={o['t']:<9.6f} LHS={o['lhs']:<12.6e} "
                      f"RHS11={o['rhs11']:<12.6e} RHS125={o['rhs125']:<12.6e} c_eff={o['ceff']:.5f}{flag}")

main()
