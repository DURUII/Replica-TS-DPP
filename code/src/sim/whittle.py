"""Whittle index for this model's per-arm subproblem.

The arm is two-dimensional -- (event age x, copy age y) -- because a pull installs
Y := X + 1 rather than resetting to 1. That is exactly why Hsu's closed form, derived
for a reset-to-1 subproblem, does not transfer here.

Arm MDP
-------
  state (x, y), x, y in {0..K-1}, flattened index = x*K + y
  reward r(x, y) = -gamma*y   (same under both actions; gamma factors out)
  x' = 0 w.p. theta, min(x+1, K-1) w.p. 1-theta      (exogenous, hence restless)
  y' = min(y+1, K-1) if passive ; min(x+1, K-1) if active

The numerical core (subsidy bisection plus indexability certification) is delegated to
markovianbandit-pkg (Gast, INRIA).
"""
import numpy as np
from markovianbandit import restless_bandit_from_P0P1_R0R1

K = 16
_CACHE = {}
_RAW = {}


def build(theta, K=K, c=1.0):
    """Return (P0, P1, R0, R1) for one arm."""
    n = K * K
    P0 = np.zeros((n, n))
    P1 = np.zeros((n, n))
    R0 = np.zeros(n)
    R1 = np.zeros(n)
    for x in range(K):
        for y in range(K):
            s = x * K + y
            for xn, p in ((0, theta), (min(x + 1, K - 1), 1 - theta)):
                if p == 0:
                    continue
                P0[s, xn * K + min(y + 1, K - 1)] += p
                P1[s, xn * K + min(x + 1, K - 1)] += p
            R0[s] = -c * y
            R1[s] = -c * y
    return P0, P1, R0, R1


def raw_table(theta, K=K):
    """K x K table of indices exactly as the solver returns them, NaNs included.

    Kept separate from `index_table` so the NaN guard in `__main__` has something left to
    find: the sanitised table is NaN-free by construction, so checking it proves nothing.
    """
    key = (round(float(np.clip(theta, 0.01, 0.99)), 2), K)
    if key not in _RAW:
        bandit = restless_bandit_from_P0P1_R0R1(*build(key[0], K))
        _RAW[key] = np.asarray(bandit.whittle_indices(), dtype=float).reshape(K, K)
    return _RAW[key]


def index_table(theta, K=K):
    """K x K table of indices, cached on a 0.01 grid of theta.

    theta = 1.0 makes the event fire every slot, so states with x > 0 become
    unreachable and the solver raises `The arm is multichain!`. Clamping to 0.99
    avoids that; every theta in [0.02, 1.0) solves cleanly, and theta -> 0 is fine.
    """
    key = (round(float(np.clip(theta, 0.01, 0.99)), 2), K)
    if key not in _CACHE:
        _CACHE[key] = np.nan_to_num(raw_table(key[0], K), nan=0.0)
    return _CACHE[key]


if __name__ == "__main__":
    # `nan=` reads the raw solver output: the arms should be indexable on the whole grid,
    # so a nonzero count means the subsidy bisection failed somewhere and those states are
    # being scored 0 by `index_table`'s sanitiser rather than by the index.
    for theta in (0.25, 0.5, 0.839):
        raw = raw_table(theta)
        tab = index_table(theta)
        nan = int(np.isnan(raw).sum())
        xm, ym = np.meshgrid(np.arange(K), np.arange(K), indexing="ij")
        cx = np.corrcoef(xm.ravel(), tab.ravel())[0, 1]
        cy = np.corrcoef(ym.ravel(), tab.ravel())[0, 1]
        print(f"theta={theta}: nan={nan} "
              f"corr(index,x)={cx:+.3f} corr(index,y)={cy:+.3f}  "
              f"{'correct direction' if cx < 0 < cy else 'WRONG direction'}")
