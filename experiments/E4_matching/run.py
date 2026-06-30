"""E4: gated steering moves one active point while parking the inactive ones (Proposition 4.2).

Tests claim:exp-e4-matching. The perceptron gate g(x) = (<a, x> - tau)_+ is identically zero on a
spherical cap (where the inactive points are parked) and positive outside it (where the active point
sits). The field x' = g(x) P_x^perp z then drives only the active point, toward the drift target z,
while the inactive points do not move. We verify the active point reaches z within eps and every
inactive point stays fixed within eps. This is the selective-motion core of the gather/corridor/
restore construction.

Run:  uv run python -m E4_matching.run
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


def main() -> int:
    rng = np.random.default_rng(SEED)
    d, M = 3, 6

    # parking direction and gate threshold: inactive cap is {<a,x> >= cos(rho)} i.e. near `a`
    a = np.zeros(d); a[0] = 1.0
    rho = 3 * np.pi / 16          # paper's parking cap radius
    tau = np.cos(rho)             # gate zero on B(a, rho): there <a,x> >= cos(rho) = tau? see below

    # We want the gate OFF on the inactive cap around `a` and ON at the active point.
    # Use gate g(x) = (tau - <a,x>)_+: zero when <a,x> >= tau (inside cap B(a,rho)), positive outside.
    inactive = sample_cap(rng, a, rho * 0.8, M - 1)        # parked points, gate off
    z = normalize(np.array([-0.6, 0.8, 0.0]))              # drift target, outside the cap
    active0 = normalize(np.array([-0.2, -0.9, 0.3]))       # active point, outside the cap

    def field(t, X):
        gate = relu(tau - X @ a)                            # 0 on the cap around a, >0 outside
        return gate[:, None] * z[None, :]

    X0 = np.vstack([inactive, active0[None, :]])
    XT = integrate(field, X0, t_span=40.0, n_steps=4000)

    inactive_move = float(geodesic_distance(XT[:M - 1], X0[:M - 1]).max())
    active_to_target = float(geodesic_distance(XT[M - 1][None, :], z[None, :])[0])

    eps = 0.05
    passed = inactive_move < eps and active_to_target < eps

    result = Result(
        name="E4_matching",
        claim="claim:exp-e4-matching",
        seed=SEED,
        passed=passed,
        criterion=(
            f"inactive points stay fixed (max move < eps={eps}) and the active point reaches the "
            f"target (geodesic distance < eps={eps})"
        ),
        metrics={
            "inactive_max_move": inactive_move,
            "active_to_target": active_to_target,
            "M": M,
        },
    )
    result.write(RESULTS)
    announce(result)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
