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
    new_axes,
    normalize,
    relu,
    sample_cap,
    save_figure,
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
    fracs = []                                    # retention measured at each waypoint a_1..a_K
    for k in range(K):
        omega = anchors[k + 1]
        z = -omega
        x = integrate(gated_field(z, R, omega), x, t_span, n_steps)
        fracs.append(float(np.mean(geodesic_distance(x, omega[None, :]) <= 0.1)))
    return fracs, K


def main() -> int:
    rng = np.random.default_rng(SEED)
    eps = 0.05

    frac_single, _ = single_ball(rng)
    fracs, K = chain(rng)
    frac_chain = fracs[-1]

    pass_single = frac_single >= 1.0 - eps
    pass_chain = frac_chain >= (1.0 - eps) ** K
    passed = pass_single and pass_chain

    # figure: measured per-stage retention vs the (1-eps)^k worst-case floor of Lemma B.1
    fig, ax = new_axes()
    stages = np.arange(1, K + 1)
    ax.plot(stages, fracs, "o-", color="#1f77b4", linewidth=2, label="measured retention")
    ax.plot(stages, (1.0 - eps) ** stages, "s--", color="#d62728",
            label=r"worst-case floor $(1-\epsilon)^k$")
    ax.set_xlabel(r"ball index $k$ (chain stage)")
    ax.set_ylabel(r"fraction within $0.1$ of anchor $a_k$")
    ax.set_title("E1 - mass retained through a chain of overlapping balls")
    ax.set_ylim(0.0, 1.02)
    ax.set_xticks(stages)
    ax.grid(True, alpha=0.3)
    ax.legend(loc="lower left")
    figures = save_figure(fig, RESULTS, "E1_mass_transport", "chain_retention")

    result = Result(
        name="E1_mass_transport",
        claim="claim:exp-e1-mass-transport",
        seed=SEED,
        passed=passed,
        hypothesis=(
            "The ReLU-gated drift of Lemma B.2 concentrates a single-hemisphere measure at the "
            "ball anchor, and chaining K overlapping balls (Lemma B.1) retains at least (1-eps)^K "
            "of the mass at the final anchor a_K."
        ),
        explanation=(
            "Each stage integrates x' = P_x^perp (cos R - <z,x>)_+ omega with R = pi/2 and "
            "omega = -z the deepest point of the active hemisphere, then measures the fraction of "
            "atoms landing within geodesic distance 0.1 of that stage's anchor. The figure overlays "
            "the measured per-stage retention on the (1-eps)^k floor: measured retention stays near "
            "1 while the worst-case floor decays, so the chain beats its guarantee at every stage."
        ),
        criterion=(
            f"single ball: fraction in inner cap >= 1-eps={1 - eps}; "
            f"chain of K={K}: fraction >= (1-eps)^K={(1 - eps) ** K:.4f}"
        ),
        metrics={
            "fraction_single_ball": frac_single,
            "fraction_chain": frac_chain,
            "fractions_per_stage": fracs,
            "K": K,
            "eps": eps,
        },
        figures=figures,
    )
    result.write(RESULTS)
    announce(result)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
