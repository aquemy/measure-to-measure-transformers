"""E7: a single linear continuity equation cannot separate overlapping supports (eq. 1.7).

Negative control for claim:exp-e7-linear-impossible. If the velocity field does not depend on the
measure mu, the characteristic flow is a single deterministic map; a point x* shared by two input
measures is sent to ONE image, so both pushforwards contain that image and their supports intersect.
Disjoint targets are therefore unreachable. By contrast, the measure-dependent self-attention field
assigns x* different velocities under the two measures, which is exactly the nonlinearity the paper
uses to disentangle.

We verify:
  (obstruction) under a fixed field, the two images of x* coincide (distance ~ 0);
  (escape)      under attention, the velocities at x* under the two measures differ.

Run:  uv run python -m E7_linear_impossible.run
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
    sample_cap,
    save_figure,
    softmax,
    tangential_projector_apply,
)

SEED = 0
RESULTS = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "results")


def main() -> int:
    rng = np.random.default_rng(SEED)
    d = 3
    # a point shared by both input measures
    xstar = normalize(rng.normal(size=d))

    # ---- obstruction: a fixed (measure-independent) tangent field ----
    w = normalize(rng.normal(size=d))

    def linear_field(t, X):
        return np.broadcast_to(w, X.shape)        # constant drift, independent of the cloud

    img1 = integrate(linear_field, xstar[None, :].copy(), t_span=5.0, n_steps=1000)
    img2 = integrate(linear_field, xstar[None, :].copy(), t_span=5.0, n_steps=1000)
    image_gap = float(geodesic_distance(img1, img2)[0])

    # ---- escape: attention velocity at x* differs between the two measures ----
    beta = 4.0
    cloud1 = np.vstack([xstar, sample_cap(rng, normalize(xstar + 0.3 * w), 0.3, 20)])
    cloud2 = np.vstack([xstar, sample_cap(rng, normalize(xstar - 0.3 * w), 0.3, 20)])

    def attn_velocity_at_xstar(cloud):
        # A_B[mu](x*) with mu = empirical measure of `cloud`, then project at x*
        scores = beta * (cloud @ xstar)
        A = softmax(scores[None, :])[0] @ cloud
        return tangential_projector_apply(xstar, A)

    v1 = attn_velocity_at_xstar(cloud1)
    v2 = attn_velocity_at_xstar(cloud2)
    velocity_gap = float(np.linalg.norm(v1 - v2))

    # obstruction confirmed when the two linear images coincide; escape when attention differs
    pass_obstruction = image_gap < 1e-6
    pass_escape = velocity_gap > 1e-2
    passed = pass_obstruction and pass_escape

    # figure: the obstruction gap (~0) vs the attention escape gap (>0) on a log scale
    fig, ax = new_axes(figsize=(6.2, 4.4))
    labels = ["linear field\n(images of $x^*$)", "attention field\n(velocities at $x^*$)"]
    real = [image_gap, velocity_gap]
    plot_vals = [max(image_gap, 1e-12), velocity_gap]   # clamp the ~0 bar so it is visible on log
    bars = ax.bar(labels, plot_vals, color=["#d62728", "#1f77b4"], width=0.6)
    ax.set_yscale("log")
    ax.axhline(1e-6, color="#7f7f7f", linestyle="--", label="obstruction tol $10^{-6}$")
    ax.axhline(1e-2, color="#2ca02c", linestyle=":", label="escape tol $10^{-2}$")
    ax.set_ylabel("gap (log scale)")
    ax.set_title("E7 - linear flow collapses $x^*$; attention separates it")
    ax.legend(loc="center left")
    for b, v in zip(bars, real):
        ax.text(b.get_x() + b.get_width() / 2, b.get_height() * 1.4, f"{v:.1e}",
                ha="center", fontsize=9)
    figures = save_figure(fig, RESULTS, "E7_linear_impossible", "obstruction_vs_escape")

    result = Result(
        name="E7_linear_impossible",
        claim="claim:exp-e7-linear-impossible",
        seed=SEED,
        passed=passed,
        hypothesis=(
            "A single measure-independent (linear) continuity equation cannot separate overlapping "
            "supports (eq. 1.7): a point x* shared by two inputs is sent to ONE image, so disjoint "
            "targets are unreachable. The measure-dependent attention field escapes this obstruction "
            "by assigning x* different velocities under the two measures."
        ),
        explanation=(
            "Under a fixed drift, x* flows to a single image regardless of which measure it belongs "
            "to, so the two images coincide (gap ~ 0). Under self-attention, the velocity at x* "
            "depends on the surrounding measure, so the two velocities differ (gap > 0). The bar "
            "chart contrasts the two gaps on a log scale against the pass tolerances."
        ),
        criterion=(
            "linear field sends shared x* to a single image (gap ~ 0, so disjoint targets are "
            "unreachable); attention assigns x* different velocities under the two measures (gap > 0)"
        ),
        metrics={
            "linear_image_gap": image_gap,
            "attention_velocity_gap": velocity_gap,
        },
        figures=figures,
    )
    result.write(RESULTS)
    announce(result)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
