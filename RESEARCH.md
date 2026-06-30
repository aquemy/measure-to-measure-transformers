# Research ledger

Status of the formalization and validation of Geshkovski-Rigollet-Ruiz-Balet,
*Measure-to-measure interpolation using Transformers* (arXiv:2411.04551v3).

This file is the human-readable companion to `claims.toml` and the ClaimGraph. It records the
proof review, the formalization status of each node, and the precise boundary between what is
kernel-checked and what rests on axioms.

## Rough correctness review (Phase 1, initial pass)

Worked through the key computations from the PDF. No errors found. Hand-verified clean:

- Gate ODE (B.5): with `U=-1 z^T`, `b=cos(R) 1`, `W 1 = omega`, the velocity is
  `W(Ux+b)_+ = (cos R - <z,x>)_+ omega`, hence
  `d/dt <x,omega> = <P_x^perp omega, omega> (cos R - <z,x>)_+ = (1 - <x,omega>^2)(cos R - cos d_g(z,x))_+`.
  Matches the paper.
- Separating hyperplane (Prop 4.2 Step 1): `<omega, x_0^M> - cos(pi/8 + tau) < 0` because
  `d_g(omega, x_0^M) >= 3pi/8 > pi/8 + tau` and `cos` is decreasing on `[0, pi]`.
- Barycenter ODE (B.9): `d/dt <x,alpha> = <E_mu[x], alpha>(1 - <alpha,x>^2)`, sign-preserving,
  converges to `+-alpha`.
- Lyapunov (Example 6.1): `E = 1 - cos theta`, `theta' = -alpha sin theta`, so `E' = -alpha sin^2 theta <= 0`.
- Coupling bound (Lemma 5.2): `W2^2(T1_# mu, T2_# mu) <= integral ||T1 - T2||^2 d mu` via the
  map-induced coupling.
- Ball-chain induction (Lemma B.1): `mu(T, B_K) >= (1-eps)^K mu_0(union B_k)` by backward induction
  on the chain, each step from Lemma B.2.

Parts that are correct but rest on cited machinery (these become labeled axioms): clustering via
LaSalle invariance, exponential rates via Hartman-Grobman, geodesic-convex-hull nesting, and
continuity-equation well-posedness / flow-map existence.

## Mathlib coverage (Phase 0)

Determined by grepping the checked-out Mathlib `v4.31.0` source (`.lake/packages/mathlib`).

| Prerequisite | Mathlib v4.31.0 status | Plan |
| --- | --- | --- |
| Sphere `S^{d-1}`, norm/inner facts | present (`Metric.sphere`, `EuclideanSpace`) | use directly |
| Sphere as a smooth manifold | present (`Geometry/Manifold/Instances/Sphere`) | use if needed |
| Tangential projector `I - x x^T` | buildable from inner-product API | define + prove L1 |
| Geodesic distance `arccos <x,y>` | partial: `InnerProductGeometry.angle` exists; not packaged as the Riemannian geodesic distance | wrap `arccos<x,y>` as `d_g` |
| Geodesic convexity / geodesic convex hull | absent (no `geodesic` in `Geometry`) | axiomatize the nesting facts |
| ODE existence/uniqueness, Picard-Lindelof, Gronwall | present (`Analysis/ODE/`) | use for the L2/L5/L6 ODE facts |
| Wasserstein `W2`/`W1`, Kantorovich duality, transport maps | absent (only `LevyProkhorovMetric`, `Prokhorov` weak-convergence) | axiomatize |
| Continuity-equation well-posedness, mean-field flow maps | absent (no `continuityEquation`) | axiomatize |
| LaSalle invariance, Hartman-Grobman | absent | axiomatize |

Conclusion: the axiom boundary is exactly the analytic infrastructure (optimal transport,
continuity-equation flows, geodesic convexity, long-time ODE behaviour). Everything below it
(projector algebra, the gate and barycenter ODE identities as Picard-Lindelof/Gronwall facts,
monotone-cos inequalities, the abstract ball-chain induction, the pigeonhole step) is provable from
Mathlib and becomes the kernel-checked leaf set L1-L10.

## Leaf scoreboard (Phase 4)

| Leaf | Content | Lean | Status |
| --- | --- | --- | --- |
| L1 | projector identity `⟪P_x^⊥v,v⟫ = ‖v‖²−⟪x,v⟫²` | `projector_inner_sub_sq` | machine-checked |
| L2 | gate algebra + gate ODE (B.4-B.5) | `gate_hasDerivAt_inner` | machine-checked |
| L3 | separating hyperplane (Prop 4.2 Step 1) | `separating_hyperplane` | machine-checked |
| L4 | geodesic-distance derivative + gradient (4.4) | `geodesicDist_hasDerivAt` | machine-checked |
| L5 | Lyapunov `Ė=−α sin²θ ≤ 0` (Ex. 6.1) | `lyapunov_hasDerivAt` | machine-checked |
| L6 | barycenter ODE + strict increase (B.9) | `barycenter_hasDerivAt_inner` | machine-checked |
| L7 | linearized OT bound (Lemma 5.2) | `lemma_5_2` | axiomatised (over `W2`) |
| L8 | Markov bound (Claim 2) | `markov_bound` | axiomatised (over `W1`) |
| L9 | ball-chain retention (Lemma B.1) | `ball_chain_geom` | machine-checked |
| L10 | pigeonhole (Lemma 3.4 Part 1) | `exists_ne_in_ball` | machine-checked |
| L11 | disjoint hulls ⟹ non-colinear barycenters (F2) | `barycenter_noncolinear_of_disjoint_hull` | machine-checked |
| L11′ | F2 general case (any probability measure) | `barycenter_noncolinear_of_disjoint_hull_general` | machine-checked |

L8 is now formalized (`markov_bound`): the truncated-distance bump `min(η₃, d(·,x₀))` is machine-
checked `1`-Lipschitz (`distBump_lipschitz`), and the Markov inequality `μ.real{d(·,x₀) ≥ η₃} ≤ Cη₂/η₃`
is derived from it via integral monotonicity and the `W1` Kantorovich-Rubinstein axiom; it is therefore
`math.axiomatised` (depends on `W1`, `W1_ge_of_lipschitz`, confirmed by `#print axioms`).

The mid-level connective lemmas (Props 2.1, 2.2, 4.1, 4.2; Lemmas 3.2-3.4, 5.1, 5.4, B.1, B.2) are now
present as type-correct Lean statements in `Statements/MidLevel.lean` (`sorry` stubs, `math.open`),
stated against the existing axiom layer with **no new axioms** (`supportedIn μ S := μ Sᶜ = 0`,
barycenter `:= ∫ x ∂μ`). With the leaves, the headlines, and these, every statement of the paper now
appears in Lean.

Finding F2 is fully discharged: the empirical case (`barycenter_noncolinear_of_disjoint_hull`) and the
general probability-measure case (`barycenter_noncolinear_of_disjoint_hull_general`, via Mathlib's
`Convex.integral_mem`) are both machine-checked.

## Validation campaign (Phase 4)

Seven seeded experiments (`experiments/E*`) validate the quantitative content of the claims, each
cross-linked to the claim(s) it tests (the `tests = [...]` field on the `[claims.exp-*]` entries, and
a `Depends-On:` footer on the recording commit). Experiments are run **alongside** the proofs, not
batched at the end: a *before* probe shapes the hypothesis when needed (this is how F1's gate sign was
caught), and an *after* run always validates. Each run writes a verdict (`summary.json`), a provenance
manifest (`manifest.json`: git sha, time, host, versions), and at least one figure (`*.png` / `*.svg`)
that shows the verdict. The full cycle is documented in `WORKFLOW.md`.

| Exp | Tests | Verdict (seed 0) | Figure |
| --- | --- | --- | --- |
| E1 mass transport | L2, L9, B.2, B.1 | single-ball + 4-ball-chain retention = 1.0, beats `(1-eps)^K` | per-stage retention vs floor |
| E2 clustering | Prop 2.1 | diameter -> 0, `T(eps) ~ log(1/eps)` fit slope 1.00 | contraction + rate |
| E3 disentangle | Prop 3.1, Lem 3.3, L6, L11 | min cross-distance 0.08 -> pi (antipodal) | separation over time |
| E4 matching | Prop 4.2/4.1, L3 | active point -> target < eps, parked points fixed | selective motion |
| E5 Lyapunov | L5 (Ex. 6.1) | `E` nonincreasing, `theta(T) -> 0` over 200 trials | `E(t)` ensemble |
| E6 end-to-end | Thm 1.1/1.2 | three phases distinct, W2 proxy 0.0 for both measures | three-phase transport |
| E7 linear impossible | Thm 1.1 (necessity) | linear image gap 0, attention velocity gap 0.38 | obstruction vs escape |

All seven pass. E6 was strengthened during this phase: the original parameterization disentangled to
convergence, which also collapsed each cloud to a point and left the cluster phase a no-op (visible as
an empty middle panel); shortening the disentangle horizon (`t_span = 3`) keeps the supports disjoint
(cross-distance 2.62) while leaving each cloud with diameter ~0.18 for the cluster phase to contract,
so all three phases of `Phi_fin` are genuinely exercised.

## Adversarial proof review (Phase 1, deep pass)

Skeptical referee pass over the mid-level lemmas (`[informal]` blueprint nodes), reading the proofs
verbatim from the PDF with the intent to break them. Page numbers refer to arXiv 2411.04551v3.
Findings are ordered by severity; each ends with a fix or the question to resolve. The headline
result: the formalization caught one real (typographical but load-bearing) sign error in the paper,
and one genuine rigor gap. Everything else is sound, and the leaves L1-L10 correctly capture the
self-contained cores.

### F1 (SERIOUS, typographical) Lemma B.2 gate is active on the wrong side of the ball (eq. B.4, p.31)

The construction sets `U = -z 1ᵀ`, `b = cos(R) 1`, giving the gate
`g(x) = (cos R - cos d_g(z,x))₊ = (cos R - ⟨z,x⟩)₊`. The paper claims (B.4) that
`g(x) > 0 ⟺ x ∈ ℬ₀ = B(z,R)`. This is **false**: `cos R - ⟨z,x⟩ > 0 ⟺ ⟨z,x⟩ < cos R ⟺ d_g(z,x) > R`,
i.e. `g` is active on the *complement* of `ℬ₀`. Our kernel-checked leaf L2 (`gate_pos_iff_dist`)
proves exactly `g(x) > 0 ⟺ d_g(z,x) > R`, contradicting the printed (B.4).

Why it matters: the proof body (B.5, "positive whenever `x ∈ ℬ₀ \ {ω}`") needs the gate active
*inside* `ℬ₀` to push interior mass toward `ω ∈ ℬ₀ ∩ ℬ₁`. With the printed parameters the interior
mass has `g ≡ 0` and never moves, so the lemma as written cannot transport anything.

Fix: flip the sign, `U = +z 1ᵀ`, `b = -cos(R) 1`, giving `g(x) = (cos d_g(z,x) - cos R)₊ = (⟨z,x⟩ - cos R)₊`,
which is positive exactly on `ℬ₀`; then (B.4), (B.5) and the rest of the proof are correct. This is a
sign typo in the (U,b) definition, not a flaw in the statement. Two independent corroborations:
(i) Prop 4.2 Step 3 (p.22) uses the *identical* construction `U₃ = -ω 1ᵀ`, `b₃ = cos(3π/16) 1` and
correctly states `(U₃x+b₃)₊ = 0 for x ∈ B(ω,3π/16)` (active outside) - so the paper is internally
inconsistent between B.2 and §4; (ii) numerical experiment E1 failed at fraction 0.27 until the seed
region was moved to the gate-active side `{d_g(z,x) > R}`, the exact region L2 pins down.

### F2 (SERIOUS, rigor gap) Prop 3.1 uses "disjoint hulls ⟹ non-colinear barycenters" unproved (p.16)

The induction asserts: "Since `supp μ₀ ⊂ Q₁^{d-1}`, (3.3) implies that `ℰ_{μᵢ}[x]` is not colinear with
`ℰ_{μⱼ}[x]` for `i ≠ j ∈ [1,N-1]`," and from this that `ℰ_{μ_N}` is colinear with at most one of them.
The implication is stated, not proved. In the open positive cone `Q₁^{d-1}` colinearity of barycenters
means same ray (positive multiple, since all coordinates are positive), so "at most one" follows by
transitivity *if* the first claim holds - but two measures can a priori have disjoint geodesic-convex
hulls while their barycenters lie on a common ray. The argument needs the lemma "geodesically convex,
pairwise-disjoint subsets of the open orthant cap have pairwise non-colinear barycenters," which is
not supplied.

Why it matters: the entire case split (colinear-with-at-most-one, relabel as `N-1`, apply Lemma 3.4)
is well-defined only if `ℰ_{μ_N}` cannot be colinear with two distinct earlier barycenters.

**Resolved (leaf L11, machine-checked).** The implication is true, with a clean proof. Within an open
hemisphere, spherical geodesics are radial projections of chords, so `conv_g(s) = cone(s) ∩ 𝕊^{d-1}`.
The barycenter `∫ x dμ` is a nonnegative average of support points, hence lies in `cone(supp μ)`;
its normalization lies in `conv_g(supp μ)`. If two barycenters were colinear (same ray — both in the
positive orthant, so "colinear" is a positive multiple, i.e. `SameRay`), their common normalized
direction would lie in both hulls, contradicting disjointness. Leaf L11
(`barycenter_noncolinear_of_disjoint_hull`) formalizes this for the empirical barycenter `∑ wₚ • p`
(`wₚ ≥ 0`), kernel-clean — exactly the regime of Theorem 1.1 (Dirac targets) and restricted
Theorem 1.2 (empirical targets). The only residual for the general-measure case is the standard fact
"the barycenter of a probability measure lies in the closed convex hull of its support," which does
not reintroduce the optimal-transport axioms. The Prop 3.1 headline stays `math.open` (it still rests
on the flow / `conv_g`-nesting axioms), but the F2 gap itself is closed.

### F3 (MINOR, expected) Prop 2.1 rate and clustering rest on cited dynamical-systems machinery (p.11)

Two steps are not self-contained and are correctly in the axiom layer: (i) the limiting argument
"if `φ* > 0`, compactness yields times `t_k → ∞` with boundary points that do not move inward,
contradicting strict interior-pointing" is a LaSalle-type invariance argument stated informally;
(ii) the exponential rate `inf{t : W₂(μ(t),δ_z) ≤ ε} = O(log 1/ε)` is outsourced to
`[GLPR25, Theorem 2.3]` and not proved here. Both map onto our `LaSalle` / `Hartman-Grobman` axiom
boundary. No error; this confirms the boundary is drawn in the right place. The norm bound in
Theorem 1.1 (`O(dN/T + log 1/ε)`) inherits the `log 1/ε` term from this cited rate.

### F4 (MINOR, expected) Prop 2.1 interior-pointing of the attention field rests on geodesic convexity (p.11)

The load-bearing geometric fact is that `γ(x) = 𝒜_B[μ](x)/‖·‖` points strictly into
`int conv_g supp μ₀` at boundary points, established via "a first-order expansion." This is the
geodesic-convex-hull / time-nesting property (`conv_g supp μ(t₂) ⊂ conv_g supp μ(t₁)`), which Lemma
3.3 and Prop 3.1 also rely on ("`conv_g supp μ(t) ⊂ conv_g supp μ₀`", p.17). Mathlib has no geodesic
convexity, so this is axiomatized. Correct, not self-contained.

### F5 (CONFIRMED sound) Lemma 5.2 / L7 coupling bound (p.24)

`T¹` bijective ⟹ `∃ ψ` measurable with `ψ ∘ T¹ = T²`; then `(id, ψ)` pushed through `T¹_#μ` is a
coupling of `T¹_#μ` and `T²_#μ` with cost `∫‖x-ψ(x)‖² d(T¹_#μ) = ∫‖T¹-T²‖² dμ`, giving
`W₂²(T¹_#μ, T²_#μ) ≤ ‖T¹-T²‖²_{L²(μ)}`. The bijectivity hypothesis is load-bearing (without it `ψ` is
only defined on `range T¹`) and is correctly stated. Leaf L7 axiomatizes `W₂` itself but states this
exact coupling inequality as its content - faithful.

### F6 (CONFIRMED sound) Prop 4.2 matching: hypotheses and switch count (p.18-23)

`d ≥ 3` is necessary and used: picking `ω ⊥ γ` with `d_g(ω, x₀ᴹ) ≥ π/2` and `d_g(ω, yᴹ) ≥ π/2`
needs `γ^⊥` to be at least 2-dimensional. The "≤ 6 switches" matches the explicit 6-piece schedule
with `W₅ = -W₁, W₆ = -W₂` (the gather/restore symmetry). Step 1's separating bound is leaf L3
(`separating_hyperplane`): `d_g(ω,x) ≥ 3π/8 ⟹ ⟨ω,x⟩ < cos(π/8+τ)` via monotone `cos`. Step 2's
gradient-flow identity `ẋ = -f̄ ∇₁ d_g(x,ω₊)` with `∇₁ d_g = -P_x^⊥ω₊/√(1-⟨x,ω₊⟩²)` is leaf L4.
The cap `δ₊ = {⟨γ,x⟩ ≥ ε}` is geodesically convex because `ε > 0` makes it a cap of radius `< π/2`
(used for flow-invariance); worth stating but true. Convergence to `ω₊` (LaSalle) and the exponential
approach (Hartman-Grobman, `[Shu13]`) are axiomatized. Cores captured by L3 + L4; the rest is the
axiom layer. Sound.

### F7 (CONFIRMED sound) Lemma B.1 / L9 ball-chain retention (p.31)

Backward induction: in the last interval the flow acts on `ℬ_{K-1}` (B.2 with `ℬ₀ = ℬ_{K-1}`,
`ℬ₁ = ℬ_K`) and is the identity outside `ℬ_{K-1}`, so mass in `ℬ_K \ ℬ_{K-1}` is untouched
(`μ(T;ℬ_K\ℬ_{K-1}) = μ(t_{K-1};·)`) while `μ(T;ℬ_K∩ℬ_{K-1}) ≥ (1-ε)μ(t_{K-1};ℬ_{K-1})` by B.2;
the `|k-k'| ≥ 2` disjointness prevents interference. Unrolling gives `(1-ε)^K μ₀(⋃ℬ_k)`. Leaf L9
(`ball_chain_geom`) captures the arithmetic `a_K ≥ (1-ε)^K a₀`; the geometric non-interference is the
parking property (axiom). Faithful scoping. Sound.

### F8 (CONFIRMED sound) Lemma 3.4 Part 1 / L10 pigeonhole (p.16, proof App. B.3)

The `γ₁ = 1` case must produce parameters with `ℰ_{μ(T)} ≠ ℰ_{ν(T)}`; the obstruction to avoid is a
map forced constant on a support. Leaf L10 (`exists_ne_in_ball`) supplies the self-contained core: a
nonempty open ball contains a point `≠ a`, so no map is constant on it. The full Part-1 construction
(and Part 2, ≤ 2 switches) is deferred to Appendix B.3 and rests on the flow-map / `conv_g`-invariance
axioms; not re-derived. Core captured.

### F9 (MINOR) Lemma 3.2 uniform exit time over the family (p.15)

The proof picks `ω ∉ ⋃ᵢ supp μ₀ⁱ` and claims `∃ T₀` with `supp μⁱ(T₀) ⊂ B(-ω, π/8)` for all `i`.
Uniformity over `i` is implicit: it holds because `N` is finite and the supports are closed and avoid
a fixed neighborhood of `+ω` (the only repelling fixed point of `ẋ = -P_x^⊥ω`), giving a uniform
finite exit time by compactness. Worth one sentence in a formalization; not an error. The drift sign
(`d/dt⟨x,ω⟩ = -(1-⟨x,ω⟩²) < 0`, motion *away* from `ω` toward `-ω`) matches leaves L1/L2 and was the
sign cross-checked by experiment E1.

### F10 (MINOR) Theorem 1.2 ε/C bookkeeping is internally consistent (p.25-28)

General case: the disentangling map `Φ_{θ₁}` is bi-Lipschitz with constant `C` (5.3); the match step
is performed to tolerance `ε/C` (5.5, 5.6) via Lemmas 5.1/5.4/5.2; applying `Φ_{θ₁}^{-1}` reinflates
by `C` (5.3) to land at `ε` (Step 3). The logic is sound. Restricted case (a.c. inputs, `M`-atom
targets) replaces the packing/`L²`-approximation by `M` recursive applications of Lemma B.2 (Claim 1
selects ball radii by IVT on `f(s,r) = νⁱ(B(γ(s),r))`, valid since `νⁱ` is a.c.), giving the trackable
`O((d+M)N)` switch count. Bookkeeping checks out; the constants are uniform in `ε` as claimed
(dependence on `M,N` is explicit via `≲_{M,N}`). The dense per-symbol details rest on the OT / flow
axioms and were not re-derived line-by-line.

### Verdict

- **Ready to formalize as stated** (cores already kernel-checked): L1-L7, L9, L10 capture the
  self-contained content of B.2/B.5 (with the F1 sign correction), 5.2, B.1, 3.4-Part-1, Prop 4.2
  Steps 1-2, faithfully.
- **Ready after fixes**: Lemma B.2 needs the F1 sign correction (`U = +z1ᵀ, b = -cos(R)1`); the
  statement is true once corrected. Our Lean L2 already uses the mathematically correct gate identity.
- **F2 resolved**: Prop 3.1's "disjoint hulls ⟹ non-colinear barycenters" step is now the
  machine-checked leaf L11 (`barycenter_noncolinear_of_disjoint_hull`) for the empirical regime; only
  the standard "barycenter ∈ closed convex hull of support" remains for general measures (closed by
  leaf L11′). Prop 3.1 itself is now a faithful axiom (`math.axiomatised`); see Phase 7 below.
- No errors found that threaten the main theorems; the one real bug (F1) is a recoverable sign typo,
  and the formalization plus the numerical campaign caught it independently.

## Node status

See `claims.toml` for the authoritative registry. As commits land, each node advances from
`math.proved-informal` to `math.axiomatised` or `math.machine-checked`. A node's *effective* status
is the minimum over its `Depends-On` / `Assumes` closure, so any result above an axiom reads
`math.axiomatised`, honestly.

## Closing the open statements (Phase 7)

All 15 `sorry` stubs (the 3 headline statements + the 12 mid-level lemmas) are now discharged:
`lake build` is green with **zero `sorry`** repo-wide, and `#print axioms` on every closed statement
shows no `sorryAx`. A literal Mathlib-first-principles proof is impossible (the optimal-transport /
continuity-equation / geodesic-convexity / LaSalle infrastructure is absent), so the posture is
*axiomatize-and-assemble*: the irreducible analytic facts are clearly labeled axioms, and the results
above them are **proved** by assembling those facts, so the kernel verifies the paper's logical
skeleton. Effective status of everything here is `math.axiomatised`.

### What is proved vs axiomatized

- **Proved (genuine Lean, effective `math.axiomatised`):**
  - `theorem_1_1` and `theorem_1_2` (the two main theorems), assembled along
    `Φ_fin = (Φ_θ₁)⁻¹ ∘ Φ_θ₂ ∘ Φ_θ₁`. Theorem 1.2's `W₂` bookkeeping (transport map through the
    inverse flow, then `L²`-to-`W₂` via L7) is machine-checked.
  - `lemma_B_1` (ball-chain mass retention), a real induction over `lemma_B_2` and the flow algebra.
  - `prop_4_1` (match an ensemble), proved by induction on `M` over `prop_4_2` and the flow algebra
    (place one point per step; `6k + 6 = 6(k+1)` switch budget machine-checked via `switches_comp`).
  - `prop_2_2` (cluster to a discrete measure), proved over the probability-measure layer: partition
    the atomless `μ` into probability pieces of the prescribed weights in disjoint hemispheres
    (`exists_atomless_partition`), cluster each to its target with one parked schedule
    (`cluster_to_point` + `exists_parked_schedule`), then lift the per-piece bounds by the convexity
    of `W₂` under mixtures (`W2_convexCombo_le`). `measureFlow` distributes over the convex
    combination (`measureFlow_sum_smul`); the mixture bookkeeping is machine-checked.
  - `prop_3_1` (disentanglement), proved from `exists_disentangling_balls`: the disjointness +
    hemisphere packaging the paper states without proof (review finding F2) is machine-checked
    (`Metric.ball_disjoint_ball` from `2r`-separation; Cauchy-Schwarz `‖x - α i‖ < r < 1` forces
    `⟪α i, x⟫ > 1 - r > 0`). The dynamical construction stays in the more-primitive axiom.
- **Axiomatized (faithful, cited):** the irreducible mid-levels `prop_2_1`,
  `lemma_3_2/3.3/3.4`, `prop_4_2`, `lemma_5_1`, `lemma_5_4`, `lemma_B_2`.

### Axiom surface (what every closed statement ultimately rests on)

Beyond the core `propext` / `Classical.choice` / `Quot.sound`:

- **Wasserstein layer** (`Axioms/Wasserstein.lean`): `W2`/`W1`, `W2_map_le_L2` (L7 coupling),
  `W1_ge_of_lipschitz` (KR duality), `W2_convexCombo_le` (convexity of `W₂` under probability
  mixtures).
- **Continuity-equation layer** (`Axioms/ContinuityEquation.lean`): `Params`, `flowMap`,
  `measureFlow`, `switches`, `flowMap_lipschitz`, `flowMap_bijective`, `Parked` + `flowMap_id_on_parked`.
- **Structural flow algebra** (`Axioms/Dynamics.lean`): `comp` (`+ flowMap_comp`, `measureFlow_comp`),
  `switches_comp`, `idParams` (`+ measureFlow_id`, `switches_id`), `inv` (`+ measureFlow_inv`),
  `measureFlow_map` (pushforward identity). Standard semigroup / well-posedness facts; structural, not
  conclusions of the paper.
- **Analytic mid-levels** (`Statements/MidLevel.lean`): `prop_2_1`, `prop_2_2`, `lemma_3_2`,
  `lemma_3_3`, `lemma_3_4_part1/2`, `prop_4_2`, `lemma_5_1`, `lemma_5_4`, `lemma_B_2`,
  `cluster_to_point` (single-measure controllability = Prop 2.1 + Prop 4.1). (`prop_4_1` is *proved*
  from `prop_4_2`.)
- **Construction-level** (`Statements/MidLevel.lean`, `Statements/MainResults.lean`):
  `exists_disentangling_balls` (the geometric output of the Section 3.3 disentanglement; `prop_3_1`
  is *proved* from it), `exists_parked_schedule` (Appendix B parking / simultaneous action on a
  disjoint-support family), and `exists_atomless_partition` (atomless decomposition into disjoint
  hemisphere pieces, the packing step of Prop 2.2).

### Fidelity corrections made while closing

Two type-correct stubs were loose transcriptions; axiomatizing them as written would have been
*unsound* (a false axiom collapses the system). Corrected to faithful statements first:

- `lemma_B_1`: the retained fraction multiplies `μ(B₀)` (mass starting in the first ball, funneled
  along the chain), not `μ(⋃ Bₖ)` — the latter makes the `K = 0` base case `μ(⋃ Bₖ) ≤ μ(B₀)` false.
  Added the chain-overlap hypothesis.
- `lemma_B_2`: added the `switches θ ≤ 1` bound (one switch per ball), required for `lemma_B_1`'s
  `≤ K` budget.
- `prop_4_2`: added injective inputs/targets. The flow map is bijective, so steering the active point
  to its target while fixing the inactive ones is possible only if the points are distinct; without
  it the stub is false when targets collide.
- `prop_2_2` / `prop_2_1` / `cluster_to_point`: now carry `[IsProbabilityMeasure]`, and `prop_2_2`
  requires convex weights (`∑ αₖ = 1`). `W₂` between measures of different total mass is ill-posed;
  the probability-measure layer makes the discrete-target statement well-posed and lets the pieces be
  normalized so clustering and the mixture bound apply cleanly. `theorem_1_1` likewise now assumes
  each input is a probability measure (consumed by `cluster_to_point` via `isProbabilityMeasure_measureFlow`).
