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

---

# Later erratum candidates

## E4. Lemma 3.4, eq. (3.2) (p.16): the printed fixing clause is refutable for atomic inputs

(Backfilled 2026-07-27; found 2026-07-04 as RESEARCH.md finding F17 and referenced as "E4" by
`claims.toml` since then, but never written into this file.) Eq. (3.2) prints the localization
clause as "the flow map is the identity off the geodesic hulls of the supports". For atomic inputs
this is refutable: a continuous flow map that is the identity off a FINITE set is the identity
everywhere, while distinct finite-support measures with equal barycenters exist, so the clause as
printed cannot hold together with the lemma's conclusion. The proof itself (App. B.3, p.35) delivers
the identity off an OPEN gate ball, i.e. off an open carrier `U` of both measures; the open-carrier
form is what the formalization states (`Statements/Lemma34Part1.lean`, discharged kernel-clean).

**Severity:** statement-level, recoverable. The proof's own open-carrier localization is the correct
statement; no downstream use needs the printed hull form.

## E5. Appendix B.3, eq. (B.16) (p.36): the `μ`/`ν` roles are swapped

(Recorded 2026-07-27, RESEARCH.md finding F23.) Eq. (B.16) as printed asserts the constructed ball
meets `supp ν(T*)` and misses `supp μ(T*)`; the derivation immediately preceding it (the one-sided
divergence of the `μ` trajectory from the shared boundary point) establishes the opposite
orientation: the ball is centered on the `μ`-flowed boundary point, carries positive `μ(T*)` mass,
and misses `supp ν(T*)`. Three independent cross-checks of the surrounding text agree. The corrected
orientation is what the formalization's admitted bridge axiom states
(`MeasureToMeasure/Leaves/AsymmetricMassGapCap.lean`, `exists_cap_nu_mass_zero_at_shared_boundary`,
claim `cap-nu-null-b16`).

**Severity:** typographical label swap, recoverable; no downstream statement changes.
