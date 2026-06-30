"""E5: Lyapunov decrease and convergence for the d=2 dynamics of Example 6.1.

Tests the leaf lemma L5 (claim:leaf-lyapunov) and Example 6.1 (claim:exp-e5-lyapunov):
for the gradient-like flow on the circle written in the angle variable theta,

    theta'(t) = -alpha sin(theta(t)),     alpha > 0,

the Lyapunov function E(theta) = 1 - cos(theta) satisfies

    E'(t) = sin(theta) theta' = -alpha sin^2(theta) <= 0,

so E decreases monotonically and theta(t) -> 0, i.e. the particle converges to the cluster
direction u_i. We integrate from many seeds and verify (a) E is nonincreasing along the flow
to numerical tolerance, and (b) theta -> 0.

Run:  uv run python -m E5_lyapunov.run
"""

from __future__ import annotations

import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from common import Result, announce, new_axes, save_figure  # noqa: E402

SEED = 0
RESULTS = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "results")


def simulate(alpha: float, theta0: float, t_span: float, n_steps: int) -> np.ndarray:
    """RK4 on theta' = -alpha sin(theta). Returns the theta trajectory."""
    dt = t_span / n_steps
    thetas = np.empty(n_steps + 1)
    thetas[0] = theta0
    th = theta0
    f = lambda t: -alpha * np.sin(t)
    for k in range(n_steps):
        k1 = f(th)
        k2 = f(th + 0.5 * dt * k1)
        k3 = f(th + 0.5 * dt * k2)
        k4 = f(th + dt * k3)
        th = th + (dt / 6.0) * (k1 + 2 * k2 + 2 * k3 + k4)
        thetas[k + 1] = th
    return thetas


def main() -> int:
    rng = np.random.default_rng(SEED)
    n_trials = 200
    t_span, n_steps = 40.0, 4000

    max_increase = 0.0           # largest positive jump in E along any trajectory
    worst_final_theta = 0.0      # largest |theta(T)| over trials (should be ~0)

    tgrid = np.linspace(0.0, t_span, n_steps + 1)
    n_plot = 60                  # subsample of trajectories to draw (keeps the figure legible)
    E_curves = []

    for i in range(n_trials):
        alpha = float(rng.uniform(0.2, 3.0))
        # avoid the unstable equilibrium theta = pi exactly; the basin of 0 is (-pi, pi)
        theta0 = float(rng.uniform(-np.pi + 0.05, np.pi - 0.05))
        thetas = simulate(alpha, theta0, t_span, n_steps)
        E = 1.0 - np.cos(thetas)
        dE = np.diff(E)
        max_increase = max(max_increase, float(dE.max()))
        worst_final_theta = max(worst_final_theta, abs(float(thetas[-1])))
        if i < n_plot:
            E_curves.append(E)

    # tolerances: monotone decrease up to RK4 round-off; convergence to the cluster
    tol_increase = 1e-9
    tol_final = 1e-3
    passed = (max_increase <= tol_increase) and (worst_final_theta <= tol_final)

    # figure: the Lyapunov function E(t) decreasing monotonically to 0 across the trial ensemble
    E_curves = np.array(E_curves)
    fig, ax = new_axes()
    for E in E_curves:
        ax.plot(tgrid, E, color="#1f77b4", alpha=0.15, linewidth=0.8)
    ax.plot(tgrid, E_curves.mean(axis=0), color="#d62728", linewidth=2.5, label="ensemble mean")
    ax.set_xlabel("time $t$")
    ax.set_ylabel(r"Lyapunov $E(\theta) = 1 - \cos\theta$")
    ax.set_title(f"E5 - Lyapunov decrease to 0 ({n_plot} of {n_trials} seeded trials)")
    ax.grid(True, alpha=0.3)
    ax.legend()
    figures = save_figure(fig, RESULTS, "E5_lyapunov", "lyapunov_decrease")

    result = Result(
        name="E5_lyapunov",
        claim="claim:exp-e5-lyapunov",
        seed=SEED,
        passed=passed,
        hypothesis=(
            "For the d=2 flow theta' = -alpha sin(theta) (Example 6.1), the Lyapunov function "
            "E(theta) = 1 - cos(theta) satisfies E'(t) = -alpha sin^2(theta) <= 0, so E decreases "
            "monotonically and theta(t) -> 0 (the cluster direction) from any start in (-pi, pi)."
        ),
        explanation=(
            "We integrate the angle ODE from 200 seeded (alpha, theta0) pairs and form "
            "E = 1 - cos(theta) along each trajectory. The figure overlays a subsample of E(t) "
            "curves (all monotonically decreasing) with the ensemble mean. The verdict checks that "
            "no step increases E beyond RK4 round-off and that every trajectory converges to 0."
        ),
        criterion=(
            f"E=1-cos(theta) nonincreasing (max step increase <= {tol_increase}) "
            f"and theta(T) -> 0 (|theta(T)| <= {tol_final}) over {n_trials} seeded trials"
        ),
        metrics={
            "max_E_increase_per_step": max_increase,
            "worst_final_abs_theta": worst_final_theta,
            "n_trials": n_trials,
        },
        figures=figures,
    )
    result.write(RESULTS)
    announce(result)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
