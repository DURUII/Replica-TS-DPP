"""The episodic restless bandit of the paper, and the four policies compared on it.

Equations follow the paper's numbering:

    Eq (2)(3)  event AoI chain, Bernoulli(theta)
    Eq (4)     copy AoI: pull arm a -> Y_a := X_a + 1, everything else ages
    Eq (9)     penalty  sum_i gamma_i * Y_i
    Eq (12)    virtual queue Z <- max(0, Z + c_a - B)
    Eq (13)    arm selection; reduces to a per-arm closed form needing no LP
    Eq (14)    Beta-Bernoulli posterior update
    Eq (16)    belief state X-hat

Policies:

    oracle     belief-DPP, theta* known                     (the paper's upper bound)
    tsdpp      belief-DPP with theta ~ posterior sample      (the paper's algorithm)
    lyapunov   the same index driven by the posterior mean   (paper baseline [20])
    whittle    the two-dimensional Whittle index of whittle.py, posterior mean

Calibration choices that the paper leaves open are collected in README.md.
"""
import numpy as np

from sim import whittle

B_DEFAULT = 0.35
K = whittle.K


def select(policy, theta, Xhat, Y, Z, gamma, c, V, rng):
    if policy == "whittle":
        # [24] prescribes no budget control, so the Whittle policy has no virtual queue.
        # It ends up spending about B anyway; `python src/diagnose.py cost` measures it.
        score = [gamma[i] * whittle.index_table(min(max(theta[i], 0.01), 0.99))
                 [int(np.clip(round(Xhat[i]), 0, K - 1)),
                  int(np.clip(round(Y[i]), 0, K - 1))]
                 for i in range(len(gamma))]
        return int(np.argmax(score))
    # oracle / tsdpp / lyapunov share this rule; they differ only in the theta they
    # are handed. Eq (13) for L(Z) = Z^2 / 2 IS the drift-plus-penalty rule, which is
    # why a faithful [20] ties the oracle instead of losing to it.
    return int(np.argmin(V * gamma * (Xhat - (Y + 1)) + Z * c))


def simulate(theta_true, gamma, c, m, L, policy, rng, V, B=B_DEFAULT, stream=None,
             carry=False, carry_z=False, rule=None, posterior=None):
    """One rollout. Returns (penalty per episode, mean realised cost per slot).

    `stream` is an (n, span) boolean array of real per-slot event indicators. The
    real-world setting of Fig. 5 passes one; each episode then replays a random
    length-L window of it. When `stream` is None events are Bernoulli(theta_true),
    which is the synthetic setting of Section V-A-1 -- and which is also what the
    policies are told to believe in either case, since Eq. (16) models the event age
    as geometric. The algorithm is not given the real burstiness any more than it is
    given theta*.

    `rule(theta, Xhat, Y, Z, gamma, c) -> arm` replaces `select`. `policy` still decides
    what the algorithm is told -- `theta*`, a posterior draw, or the posterior mean -- and
    whether the queue runs, so a variant policy is a `rule` plus the name of the policy it
    is being compared on the terms of. diagnose.py's variants go through here.

    `carry` decides whether the AoI state survives the episode boundary. It is the one
    choice that turns the real-world curve flat: `python src/diagnose.py carry` measures
    both settings on the same trace, and README Difference 6 has the table.

    `carry_z` is the rejected alternative -- carrying the virtual queue too. Eq. (7)
    averages the cost over one episode of length L, so Z is re-zeroed at the top of every
    episode by default. Carrying it instead makes the constraint bite forever and the
    penalty diverge; the flag exists so `diagnose.py carry` can show that rather than
    assert it. See DESIGN.md, S-1.

    `posterior` is a `[alpha, beta]` whose arrays are read as the prior and updated in
    place, so a caller can drive one episode at a time and watch Eq. (14) move. That is how
    `posterior_path` below works without a second copy of this loop.
    """
    n = len(theta_true)
    alpha = np.ones(n) if posterior is None else posterior[0]
    beta = np.ones(n) if posterior is None else posterior[1]
    penalty = np.zeros(m)
    spend = 0.0
    span = 0 if stream is None else stream.shape[1]
    X = np.zeros(n); Y = np.zeros(n)
    Z = 0.0
    for l in range(m):
        offset = 0 if stream is None else int(rng.integers(0, span - L))
        if not carry:
            X = np.zeros(n); Y = np.zeros(n)
        if not carry_z:
            Z = 0.0
        lam = np.zeros(n); tau = np.zeros(n)
        s_prev = np.zeros(n); t_prev = np.zeros(n)
        if policy == "oracle":
            theta = theta_true.copy()
        elif policy == "tsdpp":
            theta = rng.beta(alpha, beta)
        else:
            theta = alpha / (alpha + beta)          # plug-in posterior mean

        for t in range(1, L + 1):
            delta = t - tau
            m0 = (1 - theta) / theta
            Xhat = m0 + (1 - theta) ** delta * (lam - m0)               # Eq (16)
            if rule is None:
                a = select(policy, theta, Xhat, Y, Z, gamma, c, V, rng)  # Eq (13)
            else:
                a = rule(theta, Xhat, Y, Z, gamma, c)
            spend += c[a]
            Y = Y + 1
            Y[a] = X[a] + 1                                             # Eq (4)
            penalty[l] += float(gamma @ Y)                              # Eq (9)
            if policy != "whittle":
                Z = max(0.0, Z + c[a] - B)                              # Eq (12)

            n_gap = t - t_prev[a]; s = X[a]
            I = 1 if s < n_gap else 0
            alpha[a] += I                                               # Eq (14)
            beta[a] += s - (1 - I) * s_prev[a]
            s_prev[a], t_prev[a] = s, t
            lam[a], tau[a] = s, t
            if stream is None:
                X = np.where(rng.random(n) < theta_true, 0.0, X + 1)    # Eq (2),(3)
            else:
                X = np.where(stream[:, offset + t - 1], 0.0, X + 1)

    return penalty, spend / (m * L)


def draw_instance(rng, n):
    """Section V-A-1: theta ~ U[0,1], gamma ~ Dirichlet, c ~ U[0.2, 0.5]."""
    return rng.uniform(0, 1, n), rng.dirichlet(np.ones(n)), rng.uniform(0.2, 0.5, n)


def posterior_path(theta_true, gamma, c, m, L, rng, V, B=B_DEFAULT):
    """Fig. 7: one TS-DPP realisation, snapshotting the posterior after every episode.

    Returns (mean, ci_low, ci_high), each of shape (m + 1, n). Row 0 is the prior, before
    any episode has run -- the point the paper's panels start from.

    The band is the 2.5 and 97.5 percentiles of Beta(alpha, beta), which is the interval
    Eq (14)'s posterior defines. Whether it deserves its nominal 95 percent is a separate
    question, and `diagnose.py fig7` measures it rather than assuming it.

    Episodes are driven through `simulate` one at a time so that Eq (14) has exactly one
    implementation in this repository: with `m = 1` and no stream, `simulate` re-zeroes the
    same state the demonstration does and consumes the rng in the same order.
    """
    from scipy.stats import beta as BetaDist

    n = len(theta_true)
    posterior = [np.ones(n), np.ones(n)]
    out = []
    for l in range(m + 1):
        if l:
            simulate(theta_true, gamma, c, 1, L, "tsdpp", rng, V, B, posterior=posterior)
        alpha, beta = posterior
        out.append((alpha / (alpha + beta), BetaDist.ppf(0.025, alpha, beta),
                    BetaDist.ppf(0.975, alpha, beta)))
    return (np.array([o[0] for o in out]), np.array([o[1] for o in out]),
            np.array([o[2] for o in out]))
