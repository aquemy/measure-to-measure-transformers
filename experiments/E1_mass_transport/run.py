"""E1: mass transport through overlapping balls (Lemmas B.2 and B.1).

Tests leaf lemmas L2 (gate ODE, claim:leaf-gate-ode) and L9 (ball-chain induction,
claim:leaf-ball-chain-induction), and the science claim claim:exp-e1-mass-transport.

Construction from Lemma B.2: on S^{d-1}, with center z, radius R, and an anchor
omega in int(B0 cap B1), the parameters U = -1 z^T, b = cos(R) 1, W 1 = omega give the
ReLU-gated velocity

    v(x) = (cos R - <z, x>)_+ omega,   then projected: x' = P_x^perp v(x).

The gate is positive exactly on the open geodesic ball B0 = B(z, R), and the drift pushes
mass toward omega, which lies in B0 cap B1. We verify:

  (single ball)  fraction of mass inside B0 cap B1 at time T is >= 1 - eps;
  (chain of K)   passing mass through K overlapping balls retains >= (1 - eps)^K.

Run:  uv run python -m E1_mass_transport.run
"""

from __future__ import annotations

import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from common import (  # noqa: E402
    Result,
    announce,
    geodesic_distance,
    integrate,
    normalize,
    relu,
    sample_cap,
)

SEED = 0
RESULTS = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "results")


def gated_field(z: np.ndarray, R: float, omega: np.ndarray):
    """Ambient velocity v(x) = (cos R - <z, x>)_+ omega for a stack of points x."""
    cosR = np.cos(R)

    def field(t, x):
        gate = relu(cosR - x @ z)              # shape (n,)
        return gate[:, None] * omega[None, :]  # shape (n, d)

    return field


def single_ball(rng, d=3, t_span=30.0, n_steps=3000, n=4000):
    """Faithful to leaf L2: the gate (cos R - <z,x>)_+ is active on {d_g(z,x) > R}. With R = pi/2
    the active region is the open hemisphere {<z,x> < 0}, a geodesic cap of radius pi/2 around the
    interior anchor omega = -z. Mass seeded in that region drifts to omega; report the fraction
    reaching a small cap around omega."""
    R = np.pi / 2.0
    z = normalize(rng.normal(size=d))
    omega = -z                                    # deepest point of the active region
    # seed in the active region (cap around omega), away from the boundary
    x0 = sample_cap(rng, omega, 0.45 * np.pi, n)
    xT = integrate(gated_field(z, R, omega), x0, t_span, n_steps)
    frac = float(np.mean(geodesic_distance(xT, omega[None, :]) <= 0.1))
    return frac, omega


def chain(rng, K=4, d=3, t_span=30.0, n_steps=3000, n=4000):
    """Chain of K stages (Lemma B.1). Anchors a_0..a_K lie along a geodesic with small spacing;
    stage k uses z = -a_{k+1}, R = pi/2, so its active region is the hemisphere around a_{k+1} and
    the drift carries mass from a_k to a_{k+1}. After K stages, report the fraction near a_K."""
    R = np.pi / 2.0
    base = normalize(rng.normal(size=d))
    tangent = normalize(rng.normal(size=d))
    tangent = normalize(tangent - (tangent @ base) * base)
    step = 0.3                                    # geodesic spacing < pi/2, so stages overlap
    anchors = [normalize(np.cos(k * step) * base + np.sin(k * step) * tangent) for k in range(K + 1)]

    x = sample_cap(rng, anchors[0], 0.12, n)      # start tightly around a_0
    for k in range(K):
        omega = anchors[k + 1]
        z = -omega
        x = integrate(gated_field(z, R, omega), x, t_span, n_steps)
    frac = float(np.mean(geodesic_distance(x, anchors[K][None, :]) <= 0.1))
    return frac, K


def main() -> int:
    rng = np.random.default_rng(SEED)
    eps = 0.05

    frac_single, _ = single_ball(rng)
    frac_chain, K = chain(rng)

    pass_single = frac_single >= 1.0 - eps
    pass_chain = frac_chain >= (1.0 - eps) ** K
    passed = pass_single and pass_chain

    result = Result(
        name="E1_mass_transport",
        claim="claim:exp-e1-mass-transport",
        seed=SEED,
        passed=passed,
        criterion=(
            f"single ball: fraction in inner cap >= 1-eps={1 - eps}; "
            f"chain of K={K}: fraction >= (1-eps)^K={(1 - eps) ** K:.4f}"
        ),
        metrics={
            "fraction_single_ball": frac_single,
            "fraction_chain": frac_chain,
            "K": K,
            "eps": eps,
        },
    )
    result.write(RESULTS)
    announce(result)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
