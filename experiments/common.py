"""Shared sphere geometry and ODE utilities for the validation campaign.

Kept deliberately small and dependency-light (numpy only) so each experiment stays
self-contained and fast. The dynamics integrated here are the characteristics of the
continuity equation (1.3) of the paper:

    x'(t) = P_x^perp v(t, x),      P_x^perp = I - x x^T   (tangential projector),

with x constrained to the unit sphere S^{d-1}. We renormalize after each step to keep
the trajectory on the sphere despite finite-step error.
"""

from __future__ import annotations

import json
import os
from dataclasses import dataclass

import numpy as np


def normalize(x: np.ndarray) -> np.ndarray:
    """Project a nonzero vector (or stack of row vectors) onto the unit sphere."""
    n = np.linalg.norm(x, axis=-1, keepdims=True)
    return x / n


def tangential_projector_apply(x: np.ndarray, v: np.ndarray) -> np.ndarray:
    """Apply P_x^perp = I - x x^T to v, for ||x|| = 1. Row-wise over stacks."""
    coeff = np.sum(x * v, axis=-1, keepdims=True)
    return v - coeff * x


def geodesic_distance(x: np.ndarray, y: np.ndarray) -> np.ndarray:
    """Geodesic distance d_g(x, y) = arccos<x, y> on the unit sphere."""
    c = np.clip(np.sum(x * y, axis=-1), -1.0, 1.0)
    return np.arccos(c)


def relu(t: np.ndarray) -> np.ndarray:
    return np.maximum(t, 0.0)


def integrate(field, x0: np.ndarray, t_span: float, n_steps: int) -> np.ndarray:
    """RK4 integration of x' = P_x^perp field(t, x) on the sphere, renormalizing each step.

    `field(t, x)` returns the ambient velocity (before projection) for a stack of points x.
    Returns the trajectory endpoint (same shape as x0).
    """
    dt = t_span / n_steps
    x = normalize(np.asarray(x0, dtype=float))

    def rhs(t, x):
        return tangential_projector_apply(x, field(t, x))

    t = 0.0
    for _ in range(n_steps):
        k1 = rhs(t, x)
        k2 = rhs(t + 0.5 * dt, normalize(x + 0.5 * dt * k1))
        k3 = rhs(t + 0.5 * dt, normalize(x + 0.5 * dt * k2))
        k4 = rhs(t + dt, normalize(x + dt * k3))
        x = normalize(x + (dt / 6.0) * (k1 + 2 * k2 + 2 * k3 + k4))
        t += dt
    return x


def sample_cap(rng: np.ndarray, center: np.ndarray, radius: float, n: int) -> np.ndarray:
    """Sample n points uniformly-ish inside the geodesic cap B(center, radius) on S^{d-1}.

    Rejection sampling from the uniform distribution on the sphere.
    """
    d = center.shape[0]
    out = []
    while len(out) < n:
        batch = normalize(rng.normal(size=(4 * n, d)))
        keep = geodesic_distance(batch, center[None, :]) <= radius
        out.extend(list(batch[keep]))
    return np.array(out[:n])


def softmax(s: np.ndarray) -> np.ndarray:
    """Row-wise softmax."""
    s = s - s.max(axis=-1, keepdims=True)
    e = np.exp(s)
    return e / e.sum(axis=-1, keepdims=True)


def attention_ambient(beta: float):
    """Ambient self-attention field A_B[mu](x) = sum_j softmax_j(beta <x_i, x_j>) x_j for the
    empirical measure of the stack X (B = beta I). Returns a field(t, X) for `integrate`."""

    def field(t, X):
        scores = beta * (X @ X.T)         # (n, n)
        return softmax(scores) @ X        # (n, d)

    return field


def max_pairwise_geodesic(X: np.ndarray) -> float:
    """Diameter of a point cloud in the geodesic metric (max pairwise angle)."""
    G = np.clip(X @ X.T, -1.0, 1.0)
    return float(np.arccos(G).max())


def diam_after(field, X0: np.ndarray, t_span: float, n_steps: int) -> float:
    XT = integrate(field, X0, t_span, n_steps)
    return max_pairwise_geodesic(XT)


@dataclass
class Result:
    """A seeded experiment verdict, written to results/ as CKC evidence."""

    name: str
    claim: str
    seed: int
    passed: bool
    criterion: str
    metrics: dict

    def write(self, results_dir: str) -> str:
        d = os.path.join(results_dir, self.name)
        os.makedirs(d, exist_ok=True)
        summary = {
            "experiment": self.name,
            "claim": self.claim,
            "seed": self.seed,
            "passed": bool(self.passed),
            "criterion": self.criterion,
            "metrics": self.metrics,
        }
        path = os.path.join(d, "summary.json")
        with open(path, "w") as f:
            json.dump(summary, f, indent=2, sort_keys=True)
        return path


def announce(result: Result) -> None:
    verdict = "PASS" if result.passed else "FAIL"
    print(f"[{verdict}] {result.name} ({result.claim})")
    print(f"  criterion: {result.criterion}")
    for k, v in result.metrics.items():
        print(f"  {k} = {v}")
