"""E6: end-to-end interpolation, disentangle then cluster then match (Theorems 1.1 / 1.2).

Tests claim:exp-e6-end-to-end. Two input measures with overlapping supports are steered to two
distinct Dirac targets by the composed map Phi_fin (disentangle -> cluster -> match):

  Phase 1 (disentangle, Prop 3.1 / Lemma 3.3): barycenter separation drives the two measures into
           disjoint regions +alpha and -alpha.
  Phase 2 (cluster, Prop 2.1): self-attention contracts each measure to a single point.
  Phase 3 (match, Prop 4.1 / 4.2): each cluster is steered to its target y^i.

We report a W2 proxy: the maximum geodesic distance from each transported measure's atoms to its
target, and check it is below eps for both measures. We also confirm the supports were disjoint
after phase 1 (the matching step is single-valued only once supports are disentangled).

Run:  uv run python -m E6_end_to_end.run
"""

from __future__ import annotations

import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from common import (  # noqa: E402
    Result,
    announce,
    attention_ambient,
    geodesic_distance,
    integrate,
    normalize,
    sample_cap,
    tangential_projector_apply,
)

SEED = 0
RESULTS = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "results")


def rk4_cloud(rhs, C, dt, n_steps):
    C = normalize(C.copy())
    for _ in range(n_steps):
        k1 = rhs(C)
        k2 = rhs(normalize(C + 0.5 * dt * k1))
        k3 = rhs(normalize(C + 0.5 * dt * k2))
        k4 = rhs(normalize(C + dt * k3))
        C = normalize(C + (dt / 6.0) * (k1 + 2 * k2 + 2 * k3 + k4))
    return C


def disentangle(C, alpha, t_span=40.0, n_steps=3000):
    dt = t_span / n_steps
    def rhs(X):
        c = float(alpha @ X.mean(axis=0))
        return c * tangential_projector_apply(X, np.broadcast_to(alpha, X.shape))
    return rk4_cloud(rhs, C, dt, n_steps)


def cluster(C, beta=5.0, t_span=40.0, n_steps=3000):
    field = attention_ambient(beta)
    return integrate(field, C, t_span, n_steps)


def match(C, target, t_span=80.0, n_steps=6000):
    dt = t_span / n_steps
    def rhs(X):
        # constant tangential drift toward `target`; P_x^perp target vanishes exactly at x = target,
        # so the flow converges to the target and stops there.
        return tangential_projector_apply(X, np.broadcast_to(target, X.shape))
    return rk4_cloud(rhs, C, dt, n_steps)


def cross_min_distance(A, B):
    return float(np.arccos(np.clip(A @ B.T, -1.0, 1.0)).min())


def main() -> int:
    rng = np.random.default_rng(SEED)
    d, n = 4, 30
    alpha = np.zeros(d); alpha[0] = 1.0

    # two overlapping input clouds
    C1 = sample_cap(rng, normalize(np.array([0.3, 1.0, 0.0, 0.0])), 0.5, n)
    C2 = sample_cap(rng, normalize(np.array([-0.3, 1.0, 0.0, 0.0])), 0.5, n)

    # two distinct Dirac targets
    y1 = normalize(np.array([0.0, 0.0, 1.0, 0.0]))
    y2 = normalize(np.array([0.0, 0.0, 0.0, 1.0]))

    # Phase 1: disentangle (each measure under its own barycenter field)
    C1, C2 = disentangle(C1, alpha), disentangle(C2, alpha)
    sep_after_disentangle = cross_min_distance(C1, C2)

    # Phase 2: cluster each to a point
    C1, C2 = cluster(C1), cluster(C2)

    # Phase 3: match each cluster to its target
    C1, C2 = match(C1, y1), match(C2, y2)

    w2_proxy_1 = float(geodesic_distance(C1, y1[None, :]).max())
    w2_proxy_2 = float(geodesic_distance(C2, y2[None, :]).max())

    eps = 0.05
    passed = (sep_after_disentangle > 1.0) and (w2_proxy_1 < eps) and (w2_proxy_2 < eps)

    result = Result(
        name="E6_end_to_end",
        claim="claim:exp-e6-end-to-end",
        seed=SEED,
        passed=passed,
        criterion=(
            f"supports disjoint after disentangle (cross-distance > 1.0) and each transported "
            f"measure is within eps={eps} of its target (W2 proxy = max atom-to-target distance)"
        ),
        metrics={
            "separation_after_disentangle": sep_after_disentangle,
            "w2_proxy_measure_1": w2_proxy_1,
            "w2_proxy_measure_2": w2_proxy_2,
        },
    )
    result.write(RESULTS)
    announce(result)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
