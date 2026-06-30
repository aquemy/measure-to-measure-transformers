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


def single_ball(rng, d=3, R=0.9, t_span=30.0, n_steps=3000, n=4000):
    """One ball B0 = B(z, R); anchor omega interior; report fraction reaching B(omega, R/2)."""
    z = normalize(rng.normal(size=d))
    # omega: a point well inside B0 (distance ~ R/3 from z), standing in for int(B0 cap B1)
    direction = normalize(rng.normal(size=d))
    direction = normalize(direction - (direction @ z) * z)   # tangent at z
    omega = normalize(np.cos(R / 3.0) * z + np.sin(R / 3.0) * direction)

    x0 = sample_cap(rng, z, R, n)
    xT = integrate(gated_field(z, R, omega), x0, t_span, n_steps)
    # "B0 cap B1" stand-in: a small cap around the interior anchor omega
    inner_radius = R / 2.0
    frac = float(np.mean(geodesic_distance(xT, omega[None, :]) <= inner_radius))
    return frac, omega


def chain(rng, K=4, d=3, R=0.9, t_span=30.0, n_steps=3000, n=4000):
    """Pass mass through K overlapping balls; each stage drifts to the next anchor."""
    # build K anchors along a geodesic, consecutive balls overlapping
    base = normalize(rng.normal(size=d))
    tangent = normalize(rng.normal(size=d))
    tangent = normalize(tangent - (tangent @ base) * base)
    step = R / 2.0
    anchors = [normalize(np.cos(k * step) * base + np.sin(k * step) * tangent) for k in range(K + 1)]

    x = sample_cap(rng, anchors[0], R, n)
    for k in range(K):
        z = anchors[k]
        omega = anchors[k + 1]
        x = integrate(gated_field(z, R, omega), x, t_span, n_steps)
    frac = float(np.mean(geodesic_distance(x, anchors[K][None, :]) <= R / 2.0))
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
