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
    integrate_trace,
    max_pairwise_geodesic,
    new_axes,
    normalize,
    sample_cap,
    save_figure,
    tangential_projector_apply,
)

SEED = 0
RESULTS = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "results")


def rk4_cloud(rhs, C, dt, n_steps, record_every=None):
    """RK4 flow of a point cloud. Returns (C_final, states), where `states` samples the cloud
    every `record_every` steps (just [C0, C_final] when record_every is None)."""
    C = normalize(C.copy())
    states = [C.copy()]
    for stepi in range(n_steps):
        k1 = rhs(C)
        k2 = rhs(normalize(C + 0.5 * dt * k1))
        k3 = rhs(normalize(C + 0.5 * dt * k2))
        k4 = rhs(normalize(C + dt * k3))
        C = normalize(C + (dt / 6.0) * (k1 + 2 * k2 + 2 * k3 + k4))
        if record_every and (stepi + 1) % record_every == 0:
            states.append(C.copy())
    return C, states


def disentangle(C, alpha, t_span=40.0, n_steps=3000, record_every=None):
    dt = t_span / n_steps
    def rhs(X):
        c = float(alpha @ X.mean(axis=0))
        return c * tangential_projector_apply(X, np.broadcast_to(alpha, X.shape))
    return rk4_cloud(rhs, C, dt, n_steps, record_every)


def cluster(C, beta=5.0, t_span=40.0, n_steps=3000, record_every=None):
    field = attention_ambient(beta)
    _, states = integrate_trace(field, C, t_span, n_steps, record_every)
    return states[-1], states


def match(C, target, t_span=80.0, n_steps=6000, record_every=None):
    dt = t_span / n_steps
    def rhs(X):
        # constant tangential drift toward `target`; P_x^perp target vanishes exactly at x = target,
        # so the flow converges to the target and stops there.
        return tangential_projector_apply(X, np.broadcast_to(target, X.shape))
    return rk4_cloud(rhs, C, dt, n_steps, record_every)


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

    eps = 0.05

    # Phase 1: disentangle (each measure under its own barycenter field), recording trajectories.
    # We disentangle only until the supports are disjoint (t_span=3): the barycenter field also
    # contracts each cloud toward its pole, so running it to convergence would collapse the clouds
    # and leave nothing for the cluster phase. Stopping early keeps the three phases distinct.
    t_dis = 3.0
    C1a, st1a = disentangle(C1, alpha, t_span=t_dis, record_every=30)
    C2a, st1b = disentangle(C2, alpha, t_span=t_dis, record_every=30)
    sep_after_disentangle = cross_min_distance(C1a, C2a)
    sep_curve = np.array([cross_min_distance(a, b) for a, b in zip(st1a, st1b)])

    # Phase 2: cluster each to a point
    C1b, st2a = cluster(C1a, record_every=30)
    C2b, st2b = cluster(C2a, record_every=30)
    diam1 = np.array([max_pairwise_geodesic(s) for s in st2a])
    diam2 = np.array([max_pairwise_geodesic(s) for s in st2b])

    # Phase 3: match each cluster to its target
    C1c, st3a = match(C1b, y1, record_every=60)
    C2c, st3b = match(C2b, y2, record_every=60)
    w2_curve_1 = np.array([float(geodesic_distance(s, y1[None, :]).max()) for s in st3a])
    w2_curve_2 = np.array([float(geodesic_distance(s, y2[None, :]).max()) for s in st3b])

    w2_proxy_1 = float(w2_curve_1[-1])
    w2_proxy_2 = float(w2_curve_2[-1])

    passed = (sep_after_disentangle > 1.0) and (w2_proxy_1 < eps) and (w2_proxy_2 < eps)

    # figure: the three phases side by side -- separation rises, diameters contract, W2 -> 0
    fig, (ax1, ax2, ax3) = new_axes(figsize=(15.0, 4.3), ncols=3)
    x1 = np.linspace(0.0, t_dis, len(sep_curve))
    ax1.plot(x1, sep_curve, color="#1f77b4", linewidth=2)
    ax1.axhline(1.0, color="#d62728", linestyle="--", label="disjoint threshold")
    ax1.set_title("Phase 1 - disentangle")
    ax1.set_xlabel("time $t$"); ax1.set_ylabel("min cross-measure distance")
    ax1.grid(True, alpha=0.3); ax1.legend(loc="lower right")

    x2 = np.linspace(0.0, 40.0, len(diam1))
    ax2.semilogy(x2, diam1, color="#1f77b4", linewidth=2, label="measure 1")
    ax2.semilogy(x2, diam2, color="#ff7f0e", linewidth=2, label="measure 2")
    ax2.set_title("Phase 2 - cluster")
    ax2.set_xlabel("time $t$"); ax2.set_ylabel("cloud diameter (log)")
    ax2.grid(True, which="both", alpha=0.3); ax2.legend()

    x3 = np.linspace(0.0, 80.0, len(w2_curve_1))
    ax3.semilogy(x3, w2_curve_1, color="#1f77b4", linewidth=2, label=r"measure 1 $\to y_1$")
    ax3.semilogy(x3, w2_curve_2, color="#ff7f0e", linewidth=2, label=r"measure 2 $\to y_2$")
    ax3.axhline(eps, color="#d62728", linestyle="--", label=fr"$\epsilon = {eps}$")
    ax3.set_title("Phase 3 - match")
    ax3.set_xlabel("time $t$"); ax3.set_ylabel("W2 proxy: max atom-to-target (log)")
    ax3.grid(True, which="both", alpha=0.3); ax3.legend()
    fig.suptitle("E6 - end-to-end transport:  disentangle  ->  cluster  ->  match", fontsize=13)
    figures = save_figure(fig, RESULTS, "E6_end_to_end", "three_phase")

    result = Result(
        name="E6_end_to_end",
        claim="claim:exp-e6-end-to-end",
        seed=SEED,
        passed=passed,
        hypothesis=(
            "The composed map Phi_fin = match o cluster o disentangle (Theorems 1.1 / 1.2) sends "
            "two measures with overlapping supports to two distinct Dirac targets: disentangle makes "
            "the supports disjoint, cluster collapses each to a point, and match steers each point "
            "to its target."
        ),
        explanation=(
            "We run the three phases in sequence and record one scalar per phase over time: the "
            "minimum cross-measure distance (phase 1, must exceed 1.0 so matching is single-valued), "
            "each measure's diameter (phase 2, contracts to a point), and the W2 proxy "
            "max-atom-to-target distance (phase 3, falls below eps). The three-panel figure shows "
            "the full pipeline; the verdict checks the phase-1 separation and both final W2 proxies."
        ),
        criterion=(
            f"supports disjoint after disentangle (cross-distance > 1.0) and each transported "
            f"measure is within eps={eps} of its target (W2 proxy = max atom-to-target distance)"
        ),
        metrics={
            "separation_after_disentangle": sep_after_disentangle,
            "w2_proxy_measure_1": w2_proxy_1,
            "w2_proxy_measure_2": w2_proxy_2,
        },
        figures=figures,
    )
    result.write(RESULTS)
    announce(result)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
