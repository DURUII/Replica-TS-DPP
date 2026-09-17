#!/usr/bin/env python
"""Probe 2: can mpmath represent the tiny tails, and is the symmetry
1 - I_z(a,b) = I_{1-z}(b,a) usable for log-space evaluation?"""
import mpmath as mp
mp.mp.dps = 60

print("exponent range tests")
for e in [-300, -3000, -30000, -300000]:
    x = mp.power(10, e)
    print(f"  10^{e} = {mp.nstr(x,5)}  log={mp.nstr(mp.log(x),10)}")

print()
print("regularized incomplete beta, symmetry, log")
for (a, b, z) in [(5000, 50000, 0.0909), (5000, 50000, 0.5), (500, 500, 0.5),
                  (5000, 500, 0.0909), (50, 50, 0.5), (2, 2, 0.25)]:
    A, B, Z = mp.mpf(a), mp.mpf(b), mp.mpf(z)
    I1 = mp.betainc(A, B, 0, Z, regularized=True)
    I2 = mp.betainc(B, A, 0, 1 - Z, regularized=True)
    try:
        l1 = mp.log(1 - I1)
    except Exception as ex:
        l1 = f"FAIL {ex}"
    l2 = mp.log(I2)
    print(f"a={a} b={b} z={z}: I={mp.nstr(I1,8)}  1-I={mp.nstr(1-I1,8)}  "
          f"I_(1-z)(b,a)={mp.nstr(I2,8)}  log(1-I)={l1}  log I2={mp.nstr(l2,12)}")

print()
print("checking 1-I == I_(1-z) identity at 60 dps (difference should be ~1e-60)")
for (a, b, z) in [(5000, 50000, 0.0909), (0.5, 0.5, 0.3), (7, 3, 0.9)]:
    A, B, Z = mp.mpf(a), mp.mpf(b), mp.mpf(z)
    d = (1 - mp.betainc(A, B, 0, Z, regularized=True)) - mp.betainc(B, A, 0, 1 - Z, regularized=True)
    print(f"  a={a} b={b} z={z}:  diff = {mp.nstr(d, 5)}")
