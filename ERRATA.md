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
