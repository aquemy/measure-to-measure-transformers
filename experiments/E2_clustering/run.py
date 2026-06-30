"""E2: self-attention clusters a single-hemisphere measure to a point (Proposition 2.1).

Tests claim:exp-e2-clustering. The characteristic flow x' = P_x^perp A_B[mu](x) with B = beta I and
support in an open hemisphere contracts the geodesic convex hull to a point: the cloud diameter
diam(t) -> 0. We verify (a) the final diameter is below eps, and (b) the time to reach diameter eps
grows like log(1/eps) (a linear fit of T(eps) against log(1/eps) has positive slope and small
residual), matching the O(log 1/eps) rate.

Run:  uv run python -m E2_clustering.run
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
    integrate_trace,
    max_pairwise_geodesic,
    new_axes,
    normalize,
    sample_cap,
    save_figure,
)

SEED = 0
RESULTS = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "results")


def time_to_diam(field, X0, target_diam: float, t_max: float, n_steps: int) -> float:
    """Smallest sampled time at which the cloud diameter drops below target_diam."""
    dt = t_max / n_steps
    X = normalize(X0.copy())
    from common import tangential_projector_apply

    def rhs(t, x):
        return tangential_projector_apply(x, field(t, x))

    t = 0.0
    for _ in range(n_steps):
        # RK4 step
        k1 = rhs(t, X)
        k2 = rhs(t, normalize(X + 0.5 * dt * k1))
        k3 = rhs(t, normalize(X + 0.5 * dt * k2))
        k4 = rhs(t, normalize(X + dt * k3))
        X = normalize(X + (dt / 6.0) * (k1 + 2 * k2 + 2 * k3 + k4))
        t += dt
        if max_pairwise_geodesic(X) < target_diam:
            return t
    return t_max


def main() -> int:
    rng = np.random.default_rng(SEED)
    d, n = 4, 60
    beta = 4.0
    p = normalize(rng.normal(size=d))
    X0 = sample_cap(rng, p, 0.4 * np.pi, n)        # support in an open hemisphere

    field = attention_ambient(beta)

    init_diam = max_pairwise_geodesic(X0)
    times_d, states = integrate_trace(field, X0, t_span=60.0, n_steps=4000)
    diams = np.array([max_pairwise_geodesic(s) for s in states])
    final_diam = float(diams[-1])

    # rate check: time to reach successively smaller diameters
    eps_list = [0.2, 0.1, 0.05, 0.025]
    times = [time_to_diam(field, X0, e, t_max=120.0, n_steps=6000) for e in eps_list]
    logs = np.log(1.0 / np.array(eps_list))
    # linear fit T ~ a*log(1/eps) + b
    A = np.vstack([logs, np.ones_like(logs)]).T
    coef, res, *_ = np.linalg.lstsq(A, np.array(times), rcond=None)
    slope = float(coef[0])

    eps = 0.05
    pass_contract = final_diam < eps and init_diam > 0.5
    pass_rate = slope > 0.0
    passed = pass_contract and pass_rate

    # figure: (A) diameter contracts exponentially; (B) time-to-eps is linear in log(1/eps)
    fig, (axA, axB) = new_axes(figsize=(11.0, 4.2), ncols=2)
    axA.semilogy(times_d, diams, color="#1f77b4", linewidth=2)
    axA.axhline(eps, color="#d62728", linestyle="--", label=fr"$\epsilon = {eps}$")
    axA.set_xlabel("time $t$")
    axA.set_ylabel("cloud diameter (geodesic, log scale)")
    axA.set_title("(A) diameter contraction")
    axA.grid(True, which="both", alpha=0.3)
    axA.legend()

    axB.plot(logs, times, "o", color="#1f77b4", markersize=8, label=r"measured $T(\epsilon)$")
    xs = np.linspace(float(logs.min()), float(logs.max()), 100)
    axB.plot(xs, coef[0] * xs + coef[1], "--", color="#d62728", label=fr"linear fit, slope $={slope:.2f}$")
    axB.set_xlabel(r"$\log(1/\epsilon)$")
    axB.set_ylabel(r"time to reach diameter $\epsilon$")
    axB.set_title(r"(B) $T(\epsilon) \sim \log(1/\epsilon)$")
    axB.grid(True, alpha=0.3)
    axB.legend()
    figures = save_figure(fig, RESULTS, "E2_clustering", "contraction_and_rate")

    result = Result(
        name="E2_clustering",
        claim="claim:exp-e2-clustering",
        seed=SEED,
        passed=passed,
        hypothesis=(
            "Self-attention with B = beta I on a measure supported in an open hemisphere contracts "
            "its geodesic convex hull to a single point (Proposition 2.1); the diameter decays "
            "exponentially, so the time to reach diameter eps grows like O(log(1/eps))."
        ),
        explanation=(
            "We integrate the characteristic flow x' = P_x^perp A_B[mu](x) and record the cloud "
            "diameter over time (panel A, log scale -- a straight line is exponential decay). "
            "Panel B plots the first time the diameter drops below eps against log(1/eps) for a "
            "geometric sweep of eps; a positive-slope linear fit confirms the O(log 1/eps) rate."
        ),
        criterion=(
            f"diameter contracts from {init_diam:.3f} to < eps={eps}; "
            f"time-to-eps grows ~ log(1/eps) (positive slope)"
        ),
        metrics={
            "init_diam": init_diam,
            "final_diam": final_diam,
            "rate_slope_vs_log": slope,
            "times": times,
            "eps_list": eps_list,
        },
        figures=figures,
    )
    result.write(RESULTS)
    announce(result)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
