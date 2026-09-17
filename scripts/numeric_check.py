#!/usr/bin/env python
"""Numeric FALSIFIER for the analytic claims of infocom26.pdf.

Falsifiers, not proofs.  A pass means "no counterexample found in N random trials";
a fail means "the paper's constant is wrong".  Run before writing any Lean.
"""
import math, random

random.seed(7)
TRIALS = 30000

def pmf(theta, lam, delta):
    d = {x: theta * (1 - theta) ** x for x in range(delta)}
    d[lam + delta] = (1 - theta) ** delta
    return d

def mean_direct(theta, lam, delta):
    return sum(x * p for x, p in pmf(theta, lam, delta).items())

def mean_closed(theta, lam, delta):
    q = 1 - theta
    return q / theta + q ** delta * (lam - q / theta)

def rand_params(lo=0.001, hi=0.999):
    return (random.uniform(lo, hi), random.uniform(lo, hi),
            random.randint(0, 40), random.randint(1, 40))

# ---- Eq (15): the law is a probability mass function
worst = max(abs(sum(pmf(t, l, d).values()) - 1) for t, _, l, d in
            (rand_params() for _ in range(TRIALS)))
print(f"Eq(15)  max |sum P - 1|                    : {worst:.3e}   (expect 0)")

# ---- Eq (16): closed form of the belief state
worst = max(abs(mean_direct(t, l, d) - mean_closed(t, l, d)) for t, _, l, d in
            (rand_params() for _ in range(TRIALS)))
print(f"Eq(16)  max |E_direct - closed form|       : {worst:.3e}   (expect 0)")

# ---- Eq (21): indicator form of the likelihood == case form
def lik_ind(theta, s_prev, n, s_new):
    I = 1 if s_new < n else 0
    return theta ** I * (1 - theta) ** (s_new - (1 - I) * s_prev)

def lik_case(theta, s_prev, n, s_new):
    if s_new in range(n):   return theta * (1 - theta) ** s_new
    if s_new == s_prev + n: return (1 - theta) ** n
    return 0.0

worst = 0.0
for _ in range(TRIALS):
    th, sp, n = random.uniform(0.01, .99), random.randint(0, 30), random.randint(1, 30)
    sn = random.choice(list(range(n)) + [sp + n])
    worst = max(worst, abs(lik_ind(th, sp, n, sn) - lik_case(th, sp, n, sn)))
print(f"Eq(21)  max |indicator - case form|        : {worst:.3e}   (expect 0, exact)")

# ---- Lemma 2 Eq (23) and (24): ratios must be <= 1  (and ARE tight)
w23 = w24 = 0.0
for _ in range(TRIALS):
    t, tp = random.uniform(.0001, .9999), random.uniform(.0001, .9999)
    l, d = random.randint(0, 25), random.randint(1, 25)
    dth = abs(t - tp)
    if dth < 1e-12: continue
    P, Pp = pmf(t, l, d), pmf(tp, l, d)
    sup = list(range(d)) + [l + d]
    w23 = max(w23, sum(abs(P[x] - Pp[x]) for x in sup) / (2 * d * dth))
    w24 = max(w24, sum(x * abs(P[x] - Pp[x]) for x in sup)
                   / ((d * (d - 1) / 2 + d * (l + d)) * dth))
print(f"Lemma2 (23)  max LHS/(2*delta*|dth|)        : {w23:.10f}   (must be <= 1; tight)")
print(f"Lemma2 (24)  max LHS/((d(d-1)/2+d(l+d))|dth|): {w24:.10f}  (must be <= 1; tight)")

# ---- Eq (25): sup over [0,1] of |f'| for f(th) = th(1-th)^x
worst = 0.0
for x in range(60):
    for i in range(200001):
        g = i / 200000
        v = (1 - 2 * g) if x == 0 else (1 - g) ** (x - 1) * (1 - (x + 1) * g)
        worst = max(worst, abs(v))
print(f"Eq(25)  sup|f'| for x=0..59                : {worst:.6f}   (claim <= 1)")

# ---- Eq (39): sum_{l=1}^{m} 1/sqrt(l) <= 2 sqrt(m)
worst = max(sum(1 / math.sqrt(l) for l in range(1, m + 1)) / (2 * math.sqrt(m))
            for m in range(1, 4000))
print(f"Eq(39)  max (sum 1/sqrt(l)) / (2 sqrt(m))  : {worst:.6f}   (must be <= 1)")

# ---- Eq (19)/Theorem 2 final rate: 2 L sqrt(K0 Z) + B <= 8 sqrt(L^4 Z), K0 = 100/11, Z = m logT/eta
worst = 0.0
viol = 0
for L in range(1, 20):
    for m in range(1, 20):
        for logT in (1.0, 2.0, 10.0, 100.0):
            for eta in (0.01, 0.1, 1.0, 10.0):
                if eta > L ** 4 * m:            # hηT boundary
                    continue
                Z = m * logT / eta
                B = math.sqrt(logT)             # hBle boundary (worst case)
                lhs = 2 * L * math.sqrt((100 / 11) * Z) + B
                rhs = 8 * math.sqrt(L ** 4 * Z)
                if lhs > rhs + 1e-9:
                    viol += 1
                worst = max(worst, lhs / rhs)
print(f"Theorem2 rate  max (2L√(K₀Z)+B)/(8√(L⁴Z)) : {worst:.6f}   (must be <= 1)")
print(f"Theorem2 rate  violations over grid       : {viol}       (must be 0)")
# the constant `8` itself: how close to optimal?  2*sqrt(100/11)+1 is attained at L=m=logT=eta=1,
# B=sqrt(logT); any constant below it fails on that witness.
print(f"Theorem2 const 2√(100/11)+1 (lower bd)    : {2 * math.sqrt(100 / 11) + 1:.6f}")
print(f"Theorem2 const used                       : 8.000000   (within "
      f"{(8 - 2 * math.sqrt(100 / 11) - 1) / (2 * math.sqrt(100 / 11) + 1) * 100:.2f}% of the lower bound)")
print("        ^ max ratio (2L√(K₀Z)+B)/√(L⁴Z) is 2√(100/11)+1, attained at L=m=logT=eta=1, K₀=100/11")
# remark (paper, not artifact): the paper's own radius constant √8 gives the weaker 2√8+1 = 6.657
print(f"Theorem2 const 2√8+1 (paper's √8)         : {2 * math.sqrt(8) + 1:.6f}   (2√8+1 = 6.657)")

# ---- Eq (39) collapse: sum_l sum_t delta <= L * 2 sqrt(8 m logT/eta)
# remark: this block checks the paper's own Eq (39).  The artifact's `eq39_collapse` carries the
# sharper radius constant K₀ = 100/11 in place of the paper's 8 (radicand 400/11 when folded into
# the single square root), which only weakens the RHS; the ratio below is unchanged by K₀.
worst = 0.0
viol = 0
for m in range(0, 40):
    for L in range(1, 10):
        for eta in (0.01, 0.5, 1.0, 7.0):
            for logT in (1.0, 3.0, 50.0):
                lhs = sum(L * math.sqrt(8 * logT / (eta * (l + 1))) for l in range(m))
                rhs = L * 2 * math.sqrt(8 * m * logT / eta)
                if lhs > rhs + 1e-9:
                    viol += 1
                if rhs > 0:
                    worst = max(worst, lhs / rhs)
print(f"Eq(39) collapse  max LHS/RHS              : {worst:.6f}   (must be <= 1)")
print(f"Eq(39) collapse  violations over grid     : {viol}       (must be 0)")

# ---- GAP-4: exponent trace.  prefactor Theta(L), sum-term 2 sqrt(8 T (C+D) log T)
print("GAP-4   paper eq(39) with m=T/L, eta=L/(C+D) -> 2*sqrt(8T(C+D)logT);")
print("        with prefactor Theta(L) this is O(L sqrt(T log T)), NOT O(L^1.5 sqrt(T log T)).")
