"""E3: disentangling overlapping supports by barycenter separation (Proposition 3.1 / Lemma 3.3).

Tests claim:exp-e3-disentangle. With B = 0 and V = alpha alpha^T, the field on measure mu^i is
x' = <alpha, E_{mu^i}[x]> P_x^perp alpha (eq. B.9). Two measures whose barycenters have opposite
sign along alpha are driven to the antipodal clusters +alpha and -alpha, so their initially
overlapping supports become disjoint. We verify the minimum cross-measure geodesic distance grows
from near 0 to near pi.

Run:  uv run python -m E3_disentangle.run
"""

from __future__ import annotations

import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from common import (  # noqa: E402
    Result,
    announce,
    normalize,
    sample_cap,
    tangential_projector_apply,
)

SEED = 0
RESULTS = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "results")


def cross_min_distance(A: np.ndarray, B: np.ndarray) -> float:
    G = np.clip(A @ B.T, -1.0, 1.0)
    return float(np.arccos(G).min())


def evolve_two(C1, C2, alpha, t_span, n_steps):
    """Integrate two clouds, each under x' = <alpha, mean(cloud)> P_x^perp alpha (own barycenter)."""
    dt = t_span / n_steps
    C1 = normalize(C1.copy())
    C2 = normalize(C2.copy())

    def step(C):
        c = float(alpha @ C.mean(axis=0))          # barycenter component <alpha, E_mu[x]>
        def rhs(X):
            return c * tangential_projector_apply(X, np.broadcast_to(alpha, X.shape))
        k1 = rhs(C)
        k2 = rhs(normalize(C + 0.5 * dt * k1))
        k3 = rhs(normalize(C + 0.5 * dt * k2))
        k4 = rhs(normalize(C + dt * k3))
        return normalize(C + (dt / 6.0) * (k1 + 2 * k2 + 2 * k3 + k4))

    for _ in range(n_steps):
        C1, C2 = step(C1), step(C2)
    return C1, C2


def main() -> int:
    rng = np.random.default_rng(SEED)
    d, n = 4, 40
    alpha = np.zeros(d); alpha[0] = 1.0            # separation direction e_0

    # two clouds straddling the equator: overlapping supports, opposite-sign barycenters along alpha
    c1 = normalize(np.array([0.3, 1.0, 0.0, 0.0]))
    c2 = normalize(np.array([-0.3, 1.0, 0.0, 0.0]))
    C1 = sample_cap(rng, c1, 0.5, n)
    C2 = sample_cap(rng, c2, 0.5, n)

    init_cross = cross_min_distance(C1, C2)
    C1T, C2T = evolve_two(C1, C2, alpha, t_span=40.0, n_steps=3000)
    final_cross = cross_min_distance(C1T, C2T)

    passed = init_cross < 0.2 and final_cross > 2.0   # overlapping -> near antipodal (pi ~ 3.14)

    result = Result(
        name="E3_disentangle",
        claim="claim:exp-e3-disentangle",
        seed=SEED,
        passed=passed,
        criterion=(
            "two measures with overlapping supports (min cross-distance < 0.2) become disjoint "
            "(min cross-distance > 2.0) under barycenter-separation"
        ),
        metrics={
            "init_cross_min_distance": init_cross,
            "final_cross_min_distance": final_cross,
        },
    )
    result.write(RESULTS)
    announce(result)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
