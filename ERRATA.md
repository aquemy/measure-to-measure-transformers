# Erratum note for arXiv:2411.04551v3

This file records a sign error found in the paper while building the machine-checked formalization in
this repository, together with the kernel-checked Lean lemma and the numerical experiment that
independently surface it. It is written so it can be sent to the authors as a courtesy. The error is
typographical and does not affect any theorem; the construction is correct once the sign is flipped.

## Where

Lemma B.2 (Appendix B, p.31), equation (B.4), and the parameter choice just above it.

## The statement as printed

The proof of Lemma B.2 takes, for the ball `ℬ₀ = B(z, R)` and `ω ∈ int(ℬ₀ ∩ ℬ₁)`, with `𝟙` the
all-ones vector,

  `U = -𝟙 zᵀ`,  `b = cos(R) 𝟙`,  `W 𝟙 = ω`,

so that `U x = -𝟙 (zᵀx) = -⟨z, x⟩ 𝟙` and

  `W (U x + b)₊ = (-cos d_g(z, x) + cos R)₊ · ω = (cos R - ⟨z, x⟩)₊ · ω`,

and then asserts (B.4):

  `(cos R - ⟨z, x⟩)₊ > 0  ⟺  x ∈ ℬ₀`.

## The problem

`cos R - ⟨z, x⟩ > 0  ⟺  ⟨z, x⟩ < cos R  ⟺  d_g(z, x) > R  ⟺  x ∉ ℬ₀`.

So with the printed parameters the gate is positive exactly on the **complement** of `ℬ₀`, not on
`ℬ₀`. The equivalence (B.4) is stated with the wrong side. This matters for the proof and not only
for the formula: the body of the proof (eq. B.5, "positive whenever `x ∈ ℬ₀ \ {ω}`") needs the gate
active **inside** `ℬ₀` to push the interior mass toward `ω`. With the printed parameters the interior
mass sees a zero gate and never moves, so the lemma transports nothing as written.

## The fix

Flip the sign of the parameters:

  `U = +𝟙 zᵀ`,  `b = -cos(R) 𝟙`,

which gives `U x = ⟨z, x⟩ 𝟙` and the gate `(⟨z, x⟩ - cos R)₊`, positive exactly when `⟨z, x⟩ > cos R`,
i.e. `d_g(z, x) < R`, i.e. `x ∈ ℬ₀`. With this sign, (B.4), (B.5) and the rest of the proof are correct
and the lemma holds as stated. It is a one-sign typo in the definition of `(U, b)`; no downstream
result changes.

## Independent corroboration

1. **Internal inconsistency in the paper.** Proposition 4.2, Step 3 (p.22) uses the *same* gate
   construction `U₃ = -ω 1ᵀ`, `b₃ = cos(3π/16) 1` and there states it correctly:
   `(U₃ x + b₃)₊ = 0 for x ∈ B(ω, 3π/16)` (i.e. the gate is active *outside* the ball). So §4 and
   Lemma B.2 describe the identical construction with opposite conclusions; the §4 description is the
   correct one, which pins the typo to (B.4).

2. **Machine-checked Lean lemma.** In this repository,
   `MeasureToMeasure.Leaves.gate_pos_iff_dist` (leaf L2) proves, kernel-clean, that the gate
   `(cos R - ⟨z, x⟩)₊` is positive iff `d_g(z, x) > R` — the side opposite to the printed (B.4).

3. **Numerical experiment.** Experiment E1 (gated mass transport) failed its mass-fraction criterion
   (fraction ≈ 0.27) when mass was seeded inside `B(z, R)` as the printed (B.4) suggests, and passed
   (fraction 1.0) only once the seed was placed on the gate-active region `{d_g(z, x) > R}` that L2
   identifies. The same inversion thus shows up in the proof, the formalization, and the simulation.

## Severity

Typographical, recoverable. The statement of Lemma B.2 is true after the sign flip, and no theorem
that uses it (Prop 2.2, Theorems 1.1 and 1.2) is affected. We flag it only because reproducing the
construction requires the corrected sign.

---

# Statement-level erratum candidates (added 2026-07-03)

Two further candidates surfaced by the axiom-statement fidelity audit (RESEARCH.md findings F13 and
F15). Both are statement-level: in each case the paper's PROOF is the correct object and the printed
STATEMENT overstates it. Neither affects the main theorems.

## E2. Lemma 5.1 (p.24): "invertible" is not delivered by its own proof

The lemma is printed as producing a "Lipschitz-continuous and invertible" map `ψ` with
`ψ_# μ₀^i = μ₁^i` for all `i`. The proof (Appendix B.4, p.37) builds
`ψ^i = T^i_{Φ₃} ∘ T^i ∘ (T^i_{Φ₁})^{-1}` and glues over the disentangled supports: the flow maps
`T^i_{Φ₁}, T^i_{Φ₃}` are invertible, but the per-pair transport `T^i` is an arbitrary transport map
and need not be. Invertibility is in fact unsatisfiable in general: an atomless `μ₀^i` with a
discrete `μ₁^i` is matchable, and no injective map pushes an atomless measure onto an atom.

**Severity:** statement-level, recoverable. The downstream use (Theorem 1.2 via Lemma 5.4 and the
`W₂`-vs-`L²` bound) only needs `ψ` measurable (Lipschitz, as constructed); dropping "invertible"
restores agreement between statement and proof.

## E3. Lemmas B.1/B.2 (p.31): the printed quantifier order is not supported by the proof

Both lemmas are printed as "there exist parameters `(W, U, b)` (and a time horizon) such that for
all `μ₀ ∈ P(S^{d-1})` the retention bound holds". The proof of B.2 chooses `δ` -- and with it the
effective time budget -- AFTER `μ₀` ("small enough so that `μ₀(B(z, R−δ)) ≥ (1−ε) μ₀(ℬ₀)`", p.32),
i.e. it proves the `∀ μ₀, ∃ parameters` order. The uniform order moreover looks false as printed:
for fixed parameters and horizon, a Dirac placed close enough to the rim of `ℬ₀` sees an
arbitrarily small gate and cannot reach `ℬ₀ ∩ ℬ₁` within the fixed time, violating the uniform
`(1−ε)` retention.

**Severity:** statement-level, recoverable. Every use of B.1/B.2 in the paper instantiates them at
a specific measure, so the `∀ μ₀, ∃ parameters` order (which the formalization states) suffices.
