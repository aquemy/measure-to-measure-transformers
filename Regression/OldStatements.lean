import MeasureToMeasure.Statements.MainResults

/-!
# Kernel-refuted historical axiom statements (regression suite, single source of truth)

Each `abbrev ...Sig : Prop` below transcribes a pre-repair axiom statement of this project,
**weakened to exactly what its disproof uses** (clauses the disproof discards -- switch budgets,
horizon bookkeeping, auxiliary conclusion data -- are dropped, so a re-loosening is detected even
if those clauses change shape). `Regression/Refuted/` proves each signature `→ False`
(kernel-checked forever), and `Refutations/` holds must-fail adapters deriving each signature from
the CURRENT axiom: if an adapter ever compiles, the axiom has been re-loosened to a shape the
kernel already refuted.

Provenance of the transcriptions (`git show <rev>:<file>`):
* pre-F11 statements: `4411b08^` (repaired in PR #64, finding F11);
* pre-F12 statements: `db5889f^` (repaired in PR #66, finding F12);
* pre-F14 statements: `acafe3a^` (restated over the mean-field layer in PR #69, finding F14).

Two dynamics layers exist since PR #69 (see `Statements/MidLevel.lean`): axioms whose paper
constructions are perceptron-only stayed on the linear `Params`/`measureFlow` layer; the
measure-dependent ones moved to `AttnSchedule`/`attnMeasureFlow`. For moved axioms the
regression signature is the old-shaped statement **in the current layer** (the historically
dropped hypotheses removed from the current form): that is the shape a future re-loosening
would actually produce, and each is refuted in `Regression/Refuted/`. The purely historical
linear forms of moved axioms are kept as `...LinearSig` records (disproved, but with no
must-fail adapter -- the current axiom lives on a different layer).
-/

set_option autoImplicit false

namespace Regression

open MeasureTheory MeasureToMeasure MeasureToMeasure.Axioms MeasureToMeasure.Statements
open MeasureToMeasure.Foundations (AttnSchedule attnMeasureFlow)
open MeasureToMeasure.Leaves (barycenter)
open scoped RealInnerProductSpace

/-- Pre-F11 `lemma_3_4_part1` (finding F11): only the equal-barycenter hypothesis; no
distinctness, probability, or support hypotheses. Refuted by `μ := ν`. -/
abbrev OldLemma34Part1Sig : Prop :=
  ∀ {d : ℕ} (μ ν : Measure (Eucl d)) (T : ℝ), 0 < T → barycenter μ = barycenter ν →
    ∃ θ : Params d, barycenter (measureFlow θ T μ) ≠ barycenter (measureFlow θ T ν)

/-- Post-F11 / pre-F12 `lemma_3_4_part1` (finding F12): probability, distinctness and *ambient
orthant* support, but no sphere support. Refuted by heavy-tailed orthant measures whose Bochner
barycenters are the junk value `0`. Current `lemma_3_4_part1` is still on the linear layer, so
this signature carries a live must-fail adapter. -/
abbrev OldLemma34Part1OrthantSig : Prop :=
  ∀ {d : ℕ} (μ ν : Measure (Eucl d)), IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    ∀ T : ℝ, 0 < T → μ ≠ ν →
    supportedIn μ (orthant d) → supportedIn ν (orthant d) →
    barycenter μ = barycenter ν →
    ∃ θ : Params d, barycenter (measureFlow θ T μ) ≠ barycenter (measureFlow θ T ν)

/-- Pre-F11 `lemma_3_4_part2` (finding F11), historical linear record: NO relation between the two
measures at all (conclusion weakened: switch budget dropped). Refuted by `μ := ν` and
`SameRay.rfl`. The current `lemma_3_4_part2` lives on the mean-field layer, so this record has no
must-fail adapter. -/
abbrev OldLemma34Part2LinearSig : Prop :=
  ∀ {d : ℕ} (μ ν : Measure (Eucl d)) (T : ℝ), 0 < T →
    ∃ θ : Params d,
      ¬ SameRay ℝ (barycenter (measureFlow θ T μ)) (barycenter (measureFlow θ T ν))

/-- Current-layer `lemma_3_4_part2` with the **sphere supports removed** (the F12 heavy-tails
shape on the mean-field layer; horizon and switch clauses dropped). Refuted by heavy-tailed
orthant measures: they are not sphere-supported, so `attnMeasureFlow` is the junk identity and
both barycenters stay at the junk value `0`, where `SameRay` always holds. -/
abbrev OldAttnLemma34Part2NoSphereSig : Prop :=
  ∀ {d : ℕ} (μ ν : Measure (Eucl d)), IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    ∀ T : ℝ, 0 < T → μ ≠ ν →
    supportedIn μ (orthant d) → supportedIn ν (orthant d) →
    (∃ γ : ℝ, γ ∈ Set.Ioo (0 : ℝ) 1 ∧ barycenter μ = γ • barycenter ν) →
    ∃ θ : AttnSchedule d,
      ¬ SameRay ℝ (barycenter (attnMeasureFlow θ μ)) (barycenter (attnMeasureFlow θ ν))

/-- Pre-F12 `lemma_3_2` (finding F12): every measure, no probability/sphere/cap hypotheses
(switch budget dropped). Refuted by Lebesgue `volume`. Current `lemma_3_2` is still linear, so
this signature carries a live must-fail adapter. -/
abbrev OldLemma32Sig : Prop :=
  ∀ {d : ℕ} (μ : Measure (Eucl d)) (T : ℝ), 0 < T →
    ∃ θ : Params d, supportedIn (measureFlow θ T μ) (orthant d)

/-- Current-layer `lemma_3_2` family form with the **dimension hypothesis `2 ≤ d` removed**
(finding F18). Refuted at `d = 1` (`oldLemma32Family_dimOne_false`): on `S^0 = {±ω}` every
radially-tangent block field vanishes (in dimension one, orthogonal-to-a-unit-vector forces `0`),
so the flow fixes `-ω`, which cannot reach the orthant `{+ω}` while the sphere-support and
shared-missing-cap hypotheses at `d = 1` are jointly satisfiable. The discharged `lemma_3_2`
carries `2 ≤ d` (matching the paper's `S^{d-1}, d ≥ 2` and `lemma_B_1`/`lemma_B_2`). -/
abbrev OldLemma32FamilyNoDimSig : Prop :=
  ∀ {d N : ℕ} (μ₀ : Fin N → Measure (Eucl d)),
    (∀ i, IsProbabilityMeasure (μ₀ i)) → ∀ T : ℝ, 0 < T →
    (∀ i, supportedIn (μ₀ i) (sphere d)) → SharedMissingDirection μ₀ →
    ∃ θ : Params d, switches θ ≤ 2 ∧
      ∀ i, supportedIn (measureFlow θ T (μ₀ i)) (orthant d)

/-- Pre-F12 `lemma_3_3` (finding F12), historical linear record: every measure, into a ball of
any radius. Refuted by Lebesgue `volume`. No adapter (the current `lemma_3_3` is mean-field). -/
abbrev OldLemma33LinearSig : Prop :=
  ∀ {d : ℕ} (μ : Measure (Eucl d)) (T ε : ℝ), 0 < T → 0 < ε →
    ∃ (θ : Params d) (α : Eucl d), supportedIn (measureFlow θ T μ) (Metric.ball α ε)

/-- Current-layer `lemma_3_3` with **all measure hypotheses removed** (the F12 shape on the
mean-field layer; horizon and unit-direction clauses dropped). Refuted by Lebesgue `volume`:
a non-conforming measure makes `attnMeasureFlow` the junk identity, and `volume` is not
supported in any ball. -/
abbrev OldAttnLemma33Sig : Prop :=
  ∀ {d : ℕ} (μ : Measure (Eucl d)) (T ε : ℝ), 0 < T → 0 < ε →
    ∃ (θ : AttnSchedule d) (α : Eucl d), supportedIn (attnMeasureFlow θ μ) (Metric.ball α ε)

/-- Current-layer `cluster_to_point` with the **on-sphere restriction on `z` removed** (the F12
shape on the mean-field layer; horizon and switch clauses dropped). Refuted by an off-sphere
target: the flow keeps sphere mass on the sphere, and `W₂` from a sphere-supported probability
measure to a far Dirac is bounded below. -/
abbrev OldAttnClusterSig : Prop :=
  ∀ {d : ℕ} (μ : Measure (Eucl d)), IsProbabilityMeasure μ → 3 ≤ d →
    ∀ T ε : ℝ, 0 < T → 0 < ε → ∀ z e : Eucl d, ‖e‖ = 1 →
    supportedIn μ (sphere d) → supportedIn μ {x | 0 < ⟪e, x⟫} →
    ∃ θ : AttnSchedule d, Axioms.W2 (attnMeasureFlow θ μ) (Measure.dirac z) ≤ ε

/-- Pre-F11 `lemma_5_1` with the **disjoint-supports hypotheses removed** (finding F11;
conclusion weakened from the historical `Function.Bijective ψ` -- itself unsatisfiable, finding
F13 -- to the current `Measurable ψ`, which the disproof refutes as well). Refuted by a shared
source atom with two distinct targets. -/
abbrev OldLemma51Sig : Prop :=
  ∀ {d N : ℕ} (μ₀ μ₁ : Fin N → Measure (Eucl d)),
    (∀ i, ∃ Ti : Eucl d → Eucl d, (μ₀ i).map Ti = μ₁ i) →
    ∃ ψ : Eucl d → Eucl d, Measurable ψ ∧ ∀ i, (μ₀ i).map ψ = μ₁ i

/-- Current-layer `exists_disentangling_balls` with the **pairwise-distinctness hypothesis
removed and the missing direction weakened back to the pre-F14 point form** (`⟪ω, x⟫ < 1`,
i.e. "no atom at ω"; conclusion weakened: horizon, unit-direction and transport-map clauses
dropped). Refuted by a family of two IDENTICAL Dirac measures: one schedule produces one
pushforward, which cannot be a probability measure supported in two disjoint balls. This is the
F14-class linearity-of-the-family failure mode. -/
abbrev OldAttnDisentangleSig : Prop :=
  ∀ {d : ℕ}, 3 ≤ d → ∀ {N : ℕ} (μ₀ : Fin N → Measure (Eucl d)) (T : ℝ), 0 < T →
    (∀ i, IsProbabilityMeasure (μ₀ i)) →
    (∀ i, supportedIn (μ₀ i) (sphere d)) →
    (∃ ω : Eucl d, ‖ω‖ = 1 ∧ ∀ i, supportedIn (μ₀ i) {x | ⟪ω, x⟫ < 1}) →
    ∃ (θ : AttnSchedule d) (α : Fin N → Eucl d) (r : ℝ), 0 < r ∧ r < 1 ∧
      (∀ i j, i ≠ j → 2 * r ≤ dist (α i) (α j)) ∧
      (∀ i, supportedIn (attnMeasureFlow θ (μ₀ i)) (Metric.ball (α i) r))

end Regression
