import MeasureToMeasure.Axioms.Wasserstein
import MeasureToMeasure.Axioms.ContinuityEquation
import MeasureToMeasure.Axioms.Dynamics
import MeasureToMeasure.Leaves.BarycenterNonColinear
import MeasureToMeasure.Leaves.GatedTwoCap
import MeasureToMeasure.Leaves.OrthantRotation
import MeasureToMeasure.Leaves.Lemma34Part1MeanField
import MeasureToMeasure.Leaves.AsymmetricMassGapCap
import MeasureToMeasure.Leaves.PAlignTruncate
import MeasureToMeasure.Leaves.AsymmetricCapCollapse
import MeasureToMeasure.Foundations.AtomlessSplitting
import MeasureToMeasure.Foundations.GeodesicDistance
import MeasureToMeasure.Foundations.GeodesicConvex
import MeasureToMeasure.Foundations.Attention
import MeasureToMeasure.Foundations.AttnStepExistence
import MeasureToMeasure.Statements.SupportedIn
import MeasureToMeasure.Statements.Lemma54
import MeasureToMeasure.Leaves.ValueRounding
import Mathlib.MeasureTheory.Measure.Support

/-!
# Mid-level statements: the connective lemmas of Sections 2-5 and Appendix B

The kernel-checked leaves (L1-L11) capture the self-contained computational cores, and
`Statements/MainResults.lean` states the three headline theorems. This file fills the gap: the
mid-level lemmas the paper chains together (Propositions 2.1, 2.2, 4.1, 4.2; Lemmas 3.2, 3.3, 3.4;
Lemmas 5.1, 5.4; Lemmas B.1, B.2).

## Status policy (closing the open statements)

Each mid-level result rests on machinery Mathlib does not have (continuity-equation flow existence,
LaSalle / Hartman-Grobman, optimal transport, geodesic convexity). Those are **irreducible analytic
facts**: we state them as clearly labeled `axiom`s (status `math.axiomatised`), each citing the paper
section and the classical theorem it encodes, and each `Depends-On` the kernel-checked geometric leaf
that supplies its self-contained core.

Soundness of this posture requires each axiom's STATEMENT to be true -- something no per-node
`#print axioms` check can see. Statement fidelity is therefore enforced by its own adversarial
review: candidate stubs are attacked with kernel refutation attempts, and every dropped hypothesis
found this way is restored to the paper's form before the axiom is trusted (findings F11-F16 in
`RESEARCH.md`; earlier instances: `prop_4_2`'s injectivity, `lemma_B_1`/`lemma_B_2`'s geodesic
balls).

## The two dynamics layers (finding F14)

The paper's velocity field (1.2) is *measure-dependent* through self-attention, and eq. (1.7)
shows measure dependence is essential for the family-level results. Each statement below therefore
lives on the layer its own paper construction uses:

* **Linear layer** (`Params d` / `measureFlow`, the measure-independent characteristic flow of
  `Foundations/FlowMap.lean`): statements whose paper proofs use only perceptron parameters
  (`V ≡ 0`, so the field never reads the measure) -- `lemma_3_2` (W-only rotation),
  `lemma_3_4_part1` (V ≡ 0), `prop_4_2`/`prop_4_1` (eq. (4.1)), `lemma_B_2`/`lemma_B_1`
  (Appendix B gates), and `prop_2_2` (the Section 2.2 gated construction).
* **Mean-field layer** (`AttnSchedule d` / `attnMeasureFlow`, the self-attention flow interface of
  `Foundations/Attention.lean`): statements whose paper constructions switch on attention
  (`V ≠ 0`) -- `prop_2_1` (attention clustering; discharged in `Statements/Prop21.lean`, where the
  machine-checked witness turned out to be a `V = 0` gated block), `cluster_to_point` (likewise
  discharged, in `Statements/ClusterToPoint.lean`, via three `V = 0` gated pulls), `lemma_3_3`,
  `lemma_3_4_part2`, `lemma_5_4`, `exists_parked_schedule`, and the disentanglement/main results
  in `MainResults.lean`.

The horizon convention on the mean-field layer: a schedule spans `[0, T]` through its pieces'
durations (`AttnSchedule.durationSum θ = T`); `AttnSchedule.switches` counts pieces, exactly like
the linear `switches`.

`lemma_B_1` is **proved** (not axiomatized): it is a genuine assembly of `lemma_B_2` and the
structural flow algebra (`Axioms/Dynamics.lean`) by induction on the length of the ball chain, so its
mass-retention bound is machine-checked given the single-ball transport fact.
-/

namespace MeasureToMeasure.Statements

open MeasureTheory MeasureToMeasure.Axioms
open MeasureToMeasure.Leaves (barycenter)
open MeasureToMeasure.Foundations (AttnSchedule attnMeasureFlow)
open scoped RealInnerProductSpace ENNReal

variable {d : ℕ}

/-- A family of measures has pairwise disjoint supports: a family of carrier sets `S i` (each holding
the full mass of `ν i`) that are pairwise disjoint. -/
def DisjointSupports {N : ℕ} (ν : Fin N → Measure (Eucl d)) : Prop :=
  ∃ S : Fin N → Set (Eucl d), (∀ i, supportedIn (ν i) (S i)) ∧
    Pairwise (fun i j => Disjoint (S i) (S j))

/-- There is a unit direction `ω` missed by every measure in the family *with a positive cap gap*
`δ`: full mass on `{x | ⟪ω, x⟫ ≤ 1 - δ}` (eq. 1.4-1.5). This is the faithful encoding of
`w₀ ∉ ⋃ᵢ supp(μ₀^i)`: supports are closed, so avoiding `ω` leaves a mass-free open cap.

**Fidelity (soundness):** the earlier encoding (`full mass on {⟪ω, x⟫ < 1}`) only forbade an atom
AT `ω` -- every atomless family satisfied it for every `ω` -- and made `exists_disentangling_balls`
kernel-refutable via a measure with atoms dense in the sphere minus a point (review finding F12/F14
apparatus). The gap form restores the paper's actual strength. -/
def SharedMissingDirection {N : ℕ} (μ : Fin N → Measure (Eucl d)) : Prop :=
  ∃ ω : Eucl d, ‖ω‖ = 1 ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ i, supportedIn (μ i) {x | ⟪ω, x⟫ ≤ 1 - δ}

/-- The support misses a spherical cap: some unit direction `ω` has a positive gap `δ` with
`⟪ω, x⟫ ≤ 1 - δ` on the full mass of `μ`. This is the faithful encoding of the paper's
`supp μ ⊊ S^{d-1}` hypothesis (eq. 1.4, Lemma 3.2): a closed support avoiding `ω` leaves a
mass-free open cap around `ω`. -/
def MissingCap (μ : Measure (Eucl d)) : Prop :=
  ∃ ω : Eucl d, ‖ω‖ = 1 ∧ ∃ δ : ℝ, 0 < δ ∧ supportedIn μ {x | ⟪ω, x⟫ ≤ 1 - δ}

-- `prop_2_1` (Proposition 2.1, hemisphere clustering to a Dirac) was an axiom here; it now lives,
-- discharged as a kernel-clean theorem with the same signature verbatim, in `Statements/Prop21.lean`
-- (a separate file per the `Lemma34Part1.lean` precedent: the proof consumes the
-- `Leaves/HemisphereCollapse.lean` engine, which `MidLevel` must not import). The earlier docstring
-- claim that the convergence "rests on LaSalle and Hartman-Grobman" was too pessimistic; see the
-- theorem's docstring and finding F29 in `RESEARCH.md`.

/-- **Lemma 3.2** (transport into the orthant, family form). ONE two-piece schedule moves every
member of a sphere-supported probability family with a shared missing cap into `Q₁^{d-1}`
simultaneously (the paper's own quantification: "for any `i ∈ ⟦1,N⟧` the solution `μ^i` ...
satisfies `supp μ^i(T) ⊂ Q₁^{d-1}`", p.15). The dynamics is measure-independent (`V ≡ B ≡ U ≡ 0`),
so the members share one transport map: consumers obtain it from the linear layer
(`flowMap θ T`, with `measureFlow θ T (μ₀ i) = (μ₀ i).map (flowMap θ T)` definitionally).
DISCHARGED (`math.machine-checked`): the two constant perceptron phases are realized as scaled
gated block flows and the pointwise rotation into the orthant is machine-checked in
`Leaves.exists_twoPhase_mapsTo_orthant` (push off `-ω` to a cap around `-ω`, then pull toward an
interior orthant direction `α ≠ ω`); the transfer to `supportedIn ... (orthant d)` is the
pushforward `le_measureFlow_of_mapsTo` applied to the full-mass source cap. `Depends-On` the
scaled-gated-cap leaf (`exists_scaledGatedBlock_mapsTo_cap`).

**Fidelity (soundness):** the paper's hypotheses (Lemma 3.2, p.15) are `μ₀^i ∈ P(S^{d-1})` with
`⋃_i supp μ₀^i ⊊ S^{d-1}`; the missing direction `ω` is where the rotation field `-P_x^⊥ ω` pushes
mass away from, and the shared gap is what `SharedMissingDirection` encodes (finding F12 refuted
the unrestricted per-measure stub with the Lebesgue measure; the earlier single-measure `MissingCap`
form was the interim per-member reading, upgraded here to the paper's family quantification).

Dimension hypothesis `2 ≤ d` (finding F18, load-bearing): on the `0`-sphere `S^0 = {±ω}` every
radially-tangent field vanishes, so no flow can move `δ_{-ω}` into the orthant `{+ω}` while the
missing-cap hypotheses at `d = 1` are satisfiable -- the `2 ≤ d`-free family form is FALSE, disproved
by the kernel-checked `Regression.Refuted.oldLemma32Family_dimOne_false`. The paper works on
`S^{d-1}` with `d ≥ 2` throughout; the hypothesis matches `lemma_B_1`/`lemma_B_2`.

Budget convention: Lean's `switches` counts constant PIECES of the schedule; the paper's "at most
one switch" counts discontinuities. The paper's proof runs two constant phases (`W ≡ W₁` pushing
off `-ω`, then `W ≡ W₂` pulling toward `α`), hence `switches θ ≤ 2` here.

Layer (F14): stays on the LINEAR layer faithfully -- the paper's construction sets
`V ≡ B ≡ U ≡ 0, b = 1` (p.15), so the field `P_x^⊥ (W 1)` never reads the measure. -/
theorem lemma_3_2 {N : ℕ} (μ₀ : Fin N → Measure (Eucl d))
    (hμ : ∀ i, IsProbabilityMeasure (μ₀ i)) (hd : 2 ≤ d) (T : ℝ) (hT : 0 < T)
    (hμs : ∀ i, supportedIn (μ₀ i) (sphere d))
    (hmiss : SharedMissingDirection μ₀) :
    ∃ θ : Params d, switches θ ≤ 2 ∧
      ∀ i, supportedIn (measureFlow θ T (μ₀ i)) (orthant d) := by
  obtain ⟨ω, hω, δ, hδ0, hcap⟩ := hmiss
  -- Work at `δ' = min δ 1 ∈ (0,1]`; shrinking `δ` only enlarges the cap, so the support survives.
  set δ' : ℝ := min δ 1 with hδ'def
  have hδ'0 : 0 < δ' := lt_min hδ0 one_pos
  have hδ'1 : δ' ≤ 1 := min_le_right _ _
  have hδ'le : δ' ≤ δ := min_le_left _ _
  -- The machine-checked pointwise rotation (Leaves.OrthantRotation), shared by every member.
  obtain ⟨θ, hsw, hmaps⟩ := Leaves.exists_twoPhase_mapsTo_orthant hd hω hδ'0 hδ'1 hT
  -- `orthant d` is a finite intersection of open coordinate half-spaces, hence measurable.
  have hOrthMeas : MeasurableSet (orthant d) := by
    have hrw : orthant d = ⋂ j : Fin d, {x : Eucl d | 0 < x j} := by
      ext x; simp only [orthant, Set.mem_setOf_eq, Set.mem_iInter]
    rw [hrw]
    exact MeasurableSet.iInter fun j => measurableSet_lt measurable_const (by fun_prop)
  refine ⟨θ, hsw.le, fun i => ?_⟩
  haveI := hμ i
  haveI := isProbabilityMeasure_measureFlow θ T (μ₀ i)
  -- The source cap `S` carries the full mass of `μ₀ i` (sphere support ∩ the `δ'`-cap).
  set S : Set (Eucl d) := {x | x ∈ sphere d ∧ (⟪ω, x⟫ : ℝ) ≤ 1 - δ'} with hSdef
  have hScap : (μ₀ i) Sᶜ = 0 := by
    have hcapδ' : (μ₀ i) {x | (⟪ω, x⟫ : ℝ) ≤ 1 - δ'}ᶜ = 0 := by
      refine measure_mono_null (fun x hx => ?_) (hcap i)
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hx ⊢
      exact fun h => hx (le_trans h (by linarith))
    have hcompl : Sᶜ = (sphere d)ᶜ ∪ {x | (⟪ω, x⟫ : ℝ) ≤ 1 - δ'}ᶜ := by
      rw [hSdef]; ext x
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_union, not_and_or]
    rw [hcompl]
    exact measure_union_null (hμs i) hcapδ'
  -- Full mass on `S` ⇒ orthant carries mass `1` ⇒ its complement is null.
  have hSmass1 : 1 ≤ (μ₀ i) S := by
    have hle := measure_union_le (μ := μ₀ i) S Sᶜ
    rw [Set.union_compl_self, measure_univ, hScap, add_zero] at hle
    exact hle
  have hmaps' : Set.MapsTo (flowMap θ T) S (orthant d) := hmaps
  have hbridge : (μ₀ i) S ≤ measureFlow θ T (μ₀ i) (orthant d) :=
    le_measureFlow_of_mapsTo θ hT.le (μ₀ i) hOrthMeas hmaps'
  have hfull : measureFlow θ T (μ₀ i) (orthant d) = 1 := by
    refine le_antisymm ?_ (le_trans hSmass1 hbridge)
    calc measureFlow θ T (μ₀ i) (orthant d)
        ≤ measureFlow θ T (μ₀ i) Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  show measureFlow θ T (μ₀ i) (orthant d)ᶜ = 0
  rw [measure_compl hOrthMeas (measure_ne_top _ _), measure_univ, hfull, tsub_self]

/-- **Lemma 3.3** (family form: shrink the acted member and its colinear companion, fixing the
rest). For a `Q₁`-supported probability family with pairwise fully-non-colinear barycenters, an
acted index `j`, and a companion `ν₀` whose barycenter is colinear with the `j`-th, one schedule
concentrates BOTH `ν₀` and `μ₀ j` into the `ε`-ball around the normalized `j`-th barycenter
direction while restoring every other member exactly (`μ^i(T) = μ₀^i` for `i ≠ j`, the paper's
fixing clause; net effect of the `Ψ₁⁻¹ ∘ Ψ₂ ∘ Ψ₁` conjugation of §B.2 -- the fixed members
LEAVE `Q₁` during `Ψ₁` and return, so only the endpoint identity is asserted). AXIOM
(`math.axiomatised`): the contraction is the barycenter dynamics (leaf L6) plus the missing
mean-field theory.

**Fidelity (soundness):** the paper's Lemma 3.3 (p.16) verbatim, with the ball stated Euclidean
(the paper's geodesic ball is contained in the Euclidean one of the same radius: weaker-sound) and
the target direction indexed by the acted member `j` (the paper's display mixes `j` and `N`; the
`j`-form is the one its §3.3 proof uses). The `O(d·N)` switch budget has a non-explicit constant
and stays deferred (house policy: no invented constants). The normalized direction is genuinely
unit under these hypotheses (orthant support forces a nonzero barycenter via
`inner_barycenter_gt`); the axiom does not assert it, consumers derive it. The pre-family stub was
kernel-refuted with the Lebesgue measure (F12); the single-measure interim form lacked the fixing
clause and could not drive the §3.3 induction.

Layer (F14): mean-field -- the paper's construction (B.2, p.33) switches on the value matrix
(`V(t) = ∑ α_k α_k^⊤` pieces with `W ≡ 0`), so the field reads the flowing measure's barycenter. -/
axiom lemma_3_3 {N : ℕ} (j : Fin N) (μ₀ : Fin N → Measure (Eucl d)) (ν₀ : Measure (Eucl d))
    (hμ : ∀ i, IsProbabilityMeasure (μ₀ i)) [IsProbabilityMeasure ν₀]
    (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (hμs : ∀ i, supportedIn (μ₀ i) (sphere d)) (hμo : ∀ i, supportedIn (μ₀ i) (orthant d))
    (hνs : supportedIn ν₀ (sphere d)) (hνo : supportedIn ν₀ (orthant d))
    (hnoncol : Pairwise fun i k => ∀ c : ℝ, barycenter (μ₀ i) ≠ c • barycenter (μ₀ k))
    (hνcol : ∃ c : ℝ, barycenter ν₀ = c • barycenter (μ₀ j)) :
    ∃ θ : AttnSchedule d, AttnSchedule.durationSum θ = T ∧
      supportedIn (attnMeasureFlow θ ν₀)
        (Metric.ball (‖barycenter (μ₀ j)‖⁻¹ • barycenter (μ₀ j)) ε) ∧
      supportedIn (attnMeasureFlow θ (μ₀ j))
        (Metric.ball (‖barycenter (μ₀ j)‖⁻¹ • barycenter (μ₀ j)) ε) ∧
      ∀ i, i ≠ j → attnMeasureFlow θ (μ₀ i) = μ₀ i

-- **Lemma 3.4, Part 1** (`γ₁ = 1` case) is DISCHARGED as a kernel-clean `theorem` in
-- `Statements/Lemma34Part1.lean` (FQN `MeasureToMeasure.Statements.lemma_3_4_part1`). It lives in a
-- separate module because its App. B.3 construction cites the `two_le_d_of_distinct` leaf, which
-- itself imports this file (for `orthant`), so the discharge cannot sit here without an import cycle.
-- See that file for the statement, the fidelity/soundness notes (F12/F17/F14), and the proof.

/-- **Lemma 3.4, Part 2** (`γ₁ ∈ (0,1)` case). For two **distinct** probability measures on the orthant
whose barycenters are **colinear but unequal** (`ℰ_μ = γ·ℰ_ν` for some `γ ∈ (0,1)`), at most two
switches make the barycenters FULLY non-colinear: `ℰ_{μ(T)} ≠ γ₂ · ℰ_{ν(T)}` for every real `γ₂`
(the paper's conclusion verbatim; the earlier `¬ SameRay` form was strictly weaker, allowing
antipodal colinearity -- upgraded per finding F11's fidelity note). The "disjoint
geodesic hulls ⟹ non-colinear barycenters" implication used alongside this is the machine-checked leaf
L11 (`barycenter_noncolinear_of_disjoint_hull`, review finding F2).

**Fidelity (soundness):** the hypotheses are the paper's (`μ₀, ν₀ ∈ P(Q₁^{d-1})` different, with
`ℰ_{μ₀} = γ₁ ℰ_{ν₀}`, `γ₁ ∈ (0,1)`). The original stub omitted **every** hypothesis, which makes the
statement **false**: with no relation between `μ` and `ν`, taking `μ = ν` gives coincident flowed
barycenters, and `SameRay ℝ v v` always holds, so `¬ SameRay …` is unsatisfiable for every `θ`. The
sphere support is likewise required (F12): heavy-tailed orthant measures have junk-zero Bochner
barycenters, `0 = γ • 0` satisfies the colinearity, and `SameRay ℝ 0 0` always holds. On the sphere
the barycenters are genuine and the orthant support forces them nonzero, so the initial
`γ ∈ (0,1)` colinearity has content.

Layer (F14): mean-field -- the paper's part-2 construction (§B.3) switches on the value matrix
(`B ≡ 0` but `V ≠ 0`), so the field reads the flowing measures' barycenters. The conclusion pairs
the two flows of the SAME schedule applied to the two measures (two separate mean-field systems
sharing the parameters, as in the paper).

**Support-coincidence hypothesis (`mean-field-axioms-retractability` sub-campaign), matching the
paper's own invocation context for Part 2 rather than the general statement:** `hsupp : μ.support
= ν.support` -- the paper invokes Part 2 specifically when the two supports COINCIDE (Part 1, stated
separately in `Statements/Lemma34Part1.lean`, handles `supp μ ≠ supp ν` via a different
Wasserstein-continuity argument), and the (B.16) construction runs exactly in that branch ("if
(B.15) is not satisfied", p.36). An earlier revision also carried `_hu`, an ambient
`intrinsicInterior`/`convexHull` transcription of footnote 7's non-degeneracy condition; that
transcription is kernel-unsatisfiable (finding F25, see the re-statement notes below) and is gone.

**HISTORY.** The original axiom was converted to a theorem on 2026-07-19 (PR #260) via
`Leaves/Lemma34Part1MeanField.lean`'s `barycenter_nonColinear_of_massGapCollapse_meanField`, at
the price of an added `hgenRest` rest-component hypothesis. That discharge turned out DOUBLY
vacuous: `hgenRest` is kernel-unsatisfiable for every measure pair and every `2 ≤ d` (finding
F22, `Regression/Refuted/HgenRestUnconditionallyFalse.lean`), and independently the ambient
`intrinsicInterior`/`convexHull` transcription `_hu` of footnote 7 carried since PR #239 is
kernel-unsatisfiable in conjunction with the support hypotheses (finding F25,
`Regression/Refuted/HuUnitBarycenterStrictConvexity.lean`: a unit-norm point in the ambient
intrinsic interior of a ball-confined hull collapses the hull, hence both supports, to a
singleton, forcing `μ = ν = dirac u` against `hne`).

**RE-STATED, NON-VACUOUSLY (2026-07-27, finding F26; supersedes the F22-vacuous form).**
Hypothesis surgery relative to PR #260's signature, conclusion byte-identical:

- `hgenRest` DELETED (F22) and `_hu` DELETED (F25). Fidelity delta: dropping `_hu` RETURNS the
  statement to the paper's own p.16 scope -- footnote 7 is a proof-side narrowing of the §3.3
  invocation context, and the Appendix B.3 route used here never needs it.
- `[NoAtoms μ]` ADDED: the eq.-(B.16) bridge axiom
  (`Leaves.exists_cap_nu_mass_zero_at_shared_boundary`, claim `cap-nu-null-b16`, finding F24)
  states the paper's shared-boundary-point construction for an atomless `μ0`. An honest formal
  strengthening of the printed hypothesis list, recorded in the claim's fidelity table.
- `hcol`/`hsupp` UN-underscored: genuinely consumed by `Leaves.exists_asymmetric_massgap_cap`,
  exactly the paper's own usage (Part 2's (B.16) construction runs under equal supports and
  colinear-unequal barycenters).

**Proof route (Appendix B.3, pp.35-36, with the E5 label-swap correction).** Phase 1: run the
`pAlign` alignment block at horizon `T/2`; `Leaves.exists_asymmetric_massgap_cap` (resting on the
B.16 bridge axiom) yields a time `Tstar ∈ (0, T/2]` and a spherical cap of angular radius
`arccos cosR < π/3` carrying positive flowed-`μ` mass and zero flowed-`ν` mass, and
`Leaves.attnStep_pAlign_eq_map` renders the flowed pair as `attnStep` of the truncated block
`pAlign Tstar`. Phase 2: `Leaves.exists_asymmetric_collapse_schedule` collapses the cap toward a
pole chosen off the (fixed) `ν`-barycenter line while fixing `ν` exactly (its cap mass is zero),
forcing non-colinearity for every `γ₂`. The schedule is the two blocks, so `switches = 2` (the
paper's "at most 2 switches" verbatim) and `durationSum = Tstar + (T - Tstar) = T`. The
`ν`-barycenter being nonzero is DERIVED from sphere-plus-orthant support
(`Leaves.norm_barycenter_pos_of_orthant`), not hypothesized.

Status: `math.axiomatised`, NON-vacuously so: the closure is exactly propext, Classical.choice,
Quot.sound plus the B.16 bridge axiom, and the hypothesis bundle has a kernel-checked
FULL-application witness (`arc2Measure`/`arc2Nu`, `Regression/NonVacuity/MidLevel.lean`). -/
theorem lemma_3_4_part2 (μ ν : Measure (Eucl d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [NoAtoms μ]
    (T : ℝ) (hT : 0 < T) (hne : μ ≠ ν)
    (hμs : supportedIn μ (sphere d)) (hνs : supportedIn ν (sphere d))
    (hμ : supportedIn μ (orthant d)) (hν : supportedIn ν (orthant d))
    (hcol : ∃ γ : ℝ, γ ∈ Set.Ioo (0 : ℝ) 1 ∧ barycenter μ = γ • barycenter ν)
    (hsupp : μ.support = ν.support) :
    ∃ θ : AttnSchedule d, AttnSchedule.durationSum θ = T ∧ AttnSchedule.switches θ ≤ 2 ∧
      ∀ γ₂ : ℝ, barycenter (attnMeasureFlow θ μ) ≠ γ₂ • barycenter (attnMeasureFlow θ ν) := by
  have hd2 : 2 ≤ d := Leaves.two_le_d_of_distinct hne hμs hνs hμ hν
  haveI : NeZero d := ⟨by omega⟩
  have hμint : Integrable (fun x : Eucl d => x) μ := Leaves.integrable_id_of_sphere_support hμs
  have hνint : Integrable (fun x : Eucl d => x) ν := Leaves.integrable_id_of_sphere_support hνs
  -- the ν-barycenter is nonzero (derived from sphere+orthant support, not hypothesized)
  have hνnz : barycenter ν ≠ 0 := by
    have hpos := Leaves.norm_barycenter_pos_of_orthant hνs hνint hν
    intro h0
    rw [h0, norm_zero] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨γ1, hγ1, hcoleq⟩ := hcol
  have hT2 : (0 : ℝ) < T / 2 := by linarith
  -- Phase 1: mean-field flows for the alignment block at horizon T/2, and the asymmetric cap
  obtain ⟨Φμ, hΦμ⟩ := Foundations.exists_meanFieldFlow (Leaves.pAlign (T/2) hT2.le) μ hμs
  obtain ⟨Φν, hΦν⟩ := Foundations.exists_meanFieldFlow (Leaves.pAlign (T/2) hT2.le) ν hνs
  obtain ⟨Tstar, hTstar, z, hzs, cosR, hcosR, hμpos, hνzero⟩ :=
    Leaves.exists_asymmetric_massgap_cap hμs hνs hsupp hμint hνint hγ1 hcoleq hνnz hT2 hΦμ hΦν
  -- Phase 1 as one schedule block of duration Tstar
  set p1 : Foundations.AttnParams d := Leaves.pAlign Tstar hTstar.1.le with hp1def
  have hμ'eq : Foundations.attnStep p1 μ = μ.map (Φμ Tstar) :=
    Leaves.attnStep_pAlign_eq_map μ hμs hT2.le hΦμ hTstar.1.le hTstar.2
  have hν'eq : Foundations.attnStep p1 ν = ν.map (Φν Tstar) :=
    Leaves.attnStep_pAlign_eq_map ν hνs hT2.le hΦν hTstar.1.le hTstar.2
  haveI hμ'prob : IsProbabilityMeasure (Foundations.attnStep p1 μ) :=
    Foundations.isProbabilityMeasure_attnStep p1 μ hμs
  haveI hν'prob : IsProbabilityMeasure (Foundations.attnStep p1 ν) :=
    Foundations.isProbabilityMeasure_attnStep p1 ν hνs
  have hμ's : supportedIn (Foundations.attnStep p1 μ) (sphere d) :=
    Foundations.attnStep_supportedIn_sphere p1 μ hμs
  have hν's : supportedIn (Foundations.attnStep p1 ν) (sphere d) :=
    Foundations.attnStep_supportedIn_sphere p1 ν hνs
  -- transport the cap facts to the schedule layer
  have hμ'cap := hμpos
  rw [← hμ'eq] at hμ'cap
  have hν'cap := hνzero
  rw [← hν'eq] at hν'cap
  -- Phase 2: the asymmetric collapse block of duration T - Tstar
  have hT2pos : (0 : ℝ) < T - Tstar := by
    have h := hTstar.2
    linarith
  obtain ⟨p2, hp2dur, -, hp2noncol, -, -⟩ :=
    Leaves.exists_asymmetric_collapse_schedule hd2 (Foundations.attnStep p1 μ)
      (Foundations.attnStep p1 ν) hμ's hν's hzs hcosR hμ'cap hν'cap hT2pos
  refine ⟨[p1, p2], ?_, ?_, ?_⟩
  · show AttnSchedule.durationSum [p1, p2] = T
    simp only [Foundations.AttnSchedule.durationSum, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, hp2dur, hp1def, Leaves.pAlign_duration]
    ring
  · show AttnSchedule.switches [p1, p2] ≤ 2
    simp [Foundations.AttnSchedule.switches]
  · intro γ₂
    have hflowμ : attnMeasureFlow [p1, p2] μ
        = attnMeasureFlow [p2] (Foundations.attnStep p1 μ) := rfl
    have hflowν : attnMeasureFlow [p1, p2] ν
        = attnMeasureFlow [p2] (Foundations.attnStep p1 ν) := rfl
    rw [hflowμ, hflowν]
    exact hp2noncol γ₂

/-- **Proposition 4.2** (steer one active point). With `d ≥ 3`, distinct inputs/targets, and the
inactive points (the first `M-1`) already at their targets, at most `6` switches move every input to
its target, keeping the inactive ones fixed. AXIOM (`math.axiomatised`): the gather/corridor/restore
construction is a geodesic gradient flow. Step 1 is leaf L3, the geodesic gradient is leaf L4.

The injectivity hypotheses are required for soundness: the flow map is bijective
(`flowMap_bijective`), so steering `x₀ (M-1)` to `y (M-1)` while fixing the inactive points is
possible only if the targets (and inputs) are distinct -- otherwise the map would need two preimages
for one point. The original stub omitted them.

**Fidelity (soundness):** the sphere memberships are the paper's (Proposition 4.2 steers points of
`S^{d-1}`). Without them the axiom contradicts the kernel-checked `flowMap_mem_sphere`: it would
steer `e₁` (on the sphere) to `2 • e₁` (off it), an in-system proof of `False` (review finding
F12). -/
axiom prop_4_2 (hd : 3 ≤ d) (M : ℕ) (x₀ y : Fin M → Eucl d) (T : ℝ) (hT : 0 < T)
    (hx₀s : ∀ i, x₀ i ∈ sphere d) (hys : ∀ i, y i ∈ sphere d)
    (hx₀ : Function.Injective x₀) (hy : Function.Injective y)
    (hfix : ∀ i : Fin M, (i : ℕ) < M - 1 → x₀ i = y i) :
    ∃ θ : Params d, switches θ ≤ 6 ∧ ∀ i, flowMap θ T (x₀ i) = y i

/-- **Proposition 4.1** (match an ensemble). With `d ≥ 3` and distinct inputs/targets, at most `6M`
switches steer every `x₀ i` to `y i`.

**Proved** (effective `math.axiomatised`) by induction on `M` over Proposition 4.2 and the structural
flow algebra. Base case `M = 0`: the identity schedule (`idParams`, `0` switches). Step `M = k+1`:
place the first `k` points by the induction hypothesis on the subfamily `x₀ ∘ castSucc`,
`y ∘ castSucc` (`≤ 6k` switches), giving a schedule `φ`; then one Proposition 4.2 step moves the last
point to `y (last)` while the first `k` -- now at their targets via `φ`, so the `hfix` hypothesis
holds -- stay fixed (`≤ 6` switches); compose with `comp`. The switch budget is `6k + 6 = 6(k+1)`
(`switches_comp`), and `flowMap_comp` gives the conclusion for every index at once. The injectivity
needed for the Proposition 4.2 step is exactly `flowMap φ T ∘ x₀` injective (bijective flow composed
with injective `x₀`) and `y` injective. `Depends-On prop_4_2`. -/
theorem prop_4_1 (hd : 3 ≤ d) (M : ℕ) (x₀ y : Fin M → Eucl d) (T : ℝ) (hT : 0 < T)
    (hx₀s : ∀ i, x₀ i ∈ sphere d) (hys : ∀ i, y i ∈ sphere d)
    (hx₀ : Function.Injective x₀) (hy : Function.Injective y) :
    ∃ θ : Params d, switches θ ≤ 6 * M ∧ ∀ i, flowMap θ T (x₀ i) = y i := by
  induction M with
  | zero => exact ⟨idParams d, by simp [switches_id], fun i => i.elim0⟩
  | succ k ih =>
    -- Place the first k points by the induction hypothesis on the castSucc subfamily.
    have hx₀' : Function.Injective (x₀ ∘ Fin.castSucc) := hx₀.comp (Fin.castSucc_injective k)
    have hy' : Function.Injective (y ∘ Fin.castSucc) := hy.comp (Fin.castSucc_injective k)
    obtain ⟨φ, hφsw, hφ⟩ := ih (x₀ ∘ Fin.castSucc) (y ∘ Fin.castSucc)
      (fun i => hx₀s _) (fun i => hys _) hx₀' hy'
    simp only [Function.comp_apply] at hφ
    -- Current positions of all k+1 points after φ.
    set p : Fin (k + 1) → Eucl d := fun i => flowMap φ T (x₀ i) with hp
    have hpinj : Function.Injective p := (flowMap_bijective φ T).injective.comp hx₀
    -- The flow keeps every point on the sphere.
    have hps : ∀ i, p i ∈ sphere d := fun i => flowMap_mem_sphere φ hT.le (hx₀s i)
    -- The first k points already sit at their targets, so prop_4_2's hypothesis holds.
    have hfix : ∀ i : Fin (k + 1), (i : ℕ) < (k + 1) - 1 → p i = y i := by
      intro i hi
      have hlt : (i : ℕ) < k := by omega
      calc p i = flowMap φ T (x₀ (Fin.castSucc (Fin.castLT i hlt))) := by
                rw [Fin.castSucc_castLT]
        _ = y (Fin.castSucc (Fin.castLT i hlt)) := hφ (Fin.castLT i hlt)
        _ = y i := by rw [Fin.castSucc_castLT]
    obtain ⟨ψ, hψsw, hψ⟩ := prop_4_2 hd (k + 1) p y T hT hps hys hpinj hy hfix
    refine ⟨comp φ ψ, ?_, ?_⟩
    · calc switches (comp φ ψ) ≤ switches φ + switches ψ := switches_comp φ ψ
        _ ≤ 6 * k + 6 := Nat.add_le_add hφsw hψsw
        _ = 6 * (k + 1) := by ring
    · intro i
      rw [flowMap_comp]
      exact hψ i

-- `cluster_to_point` (clustering to a prescribed point, Prop 2.1 followed by Prop 4.1) was an
-- axiom here; it now lives, discharged as a kernel-clean theorem with the same signature verbatim,
-- in `Statements/ClusterToPoint.lean` (a separate file per the `Prop21.lean` precedent: the proof
-- consumes the `Leaves/ThreePullCluster.lean` machinery, which `MidLevel` must not import). The
-- witness is a chain of three `V = 0` gated pulls relaying the mass `e → α → z` through a unit
-- vector orthogonal to both (the consumer of `3 ≤ d`), `switches = 3 ≤ 7`; see the theorem's
-- docstring and finding F30 in `RESEARCH.md`.

/-- **Measurable gluing over disjoint supports** (the reusable core of Lemma 5.1's proof). Given a
family of measures with pairwise disjoint supports and a measurable map `S i` for each member, a
single measurable map `g` agrees with each `S i` on `ν i`-almost every point. This re-exposes the
machinery `lemma_5_1` below machine-checks -- the `toMeasurable` carrier upgrade plus the
indicator-sum glue -- with the per-member a.e. agreement as the conclusion instead of pushforward
equality, so consumers needing pointwise conclusions (e.g. a universal-map companion to
`exists_parked_schedule`) can use it without re-deriving the carriers. `lemma_5_1` is now derived
from this via `Measure.map_congr`. -/
theorem exists_measurable_glue {N : ℕ} (ν : Fin N → Measure (Eucl d))
    (hdisj : DisjointSupports ν) (S : Fin N → Eucl d → Eucl d)
    (hSm : ∀ i, Measurable (S i)) :
    ∃ g : Eucl d → Eucl d, Measurable g ∧ ∀ i, g =ᵐ[ν i] S i := by
  classical
  obtain ⟨A, hAsupp, hAdisj⟩ := hdisj
  -- Measurable, full-mass carriers `C i ⊆ A i`; pairwise disjointness is inherited from `A`.
  set C : Fin N → Set (Eucl d) := fun i => (toMeasurable (ν i) (A i)ᶜ)ᶜ with hCdef
  have hCmeas : ∀ i, MeasurableSet (C i) := fun i => (measurableSet_toMeasurable _ _).compl
  have hCmass : ∀ i, ν i (C i)ᶜ = 0 := by
    intro i
    simp only [hCdef, compl_compl]
    rw [measure_toMeasurable]
    exact hAsupp i
  have hCsub : ∀ i, C i ⊆ A i := by
    intro i x hx
    simp only [hCdef, Set.mem_compl_iff] at hx
    by_contra hxA
    exact hx (subset_toMeasurable (ν i) (A i)ᶜ hxA)
  have hCdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j) := fun i j hij =>
    Disjoint.mono (hCsub i) (hCsub j) (hAdisj hij)
  -- Glue the measurable per-member maps over the disjoint carriers.
  refine ⟨fun x => ∑ i, (C i).indicator (S i) x,
    Finset.measurable_sum _ (fun i _ => (hSm i).indicator (hCmeas i)), ?_⟩
  intro i
  have hEqOn : Set.EqOn (fun x => ∑ j, (C j).indicator (S j) x) (S i) (C i) := by
    intro x hx
    show ∑ j, (C j).indicator (S j) x = S i x
    rw [Finset.sum_eq_single i
        (fun j _ hji => Set.indicator_of_notMem
          (Set.disjoint_left.mp (hCdisj i j hji.symm) hx) (S j))
        (fun hi => absurd (Finset.mem_univ i) hi)]
    exact Set.indicator_of_mem hx (S i)
  exact Filter.eventuallyEq_of_mem (mem_ae_iff.mpr (hCmass i)) hEqOn

/-- **Lemma 5.1** (transport map after disentanglement). If the pairs are **disentangled** -- both the
source family `μ₀` and the target family `μ₁` have pairwise disjoint supports (this is what Proposition
3.1 achieves for `μ^i₀` and `μ^i₁` in the paper) -- and each pair is individually matchable, then a
single measurable map matches them all. DISCHARGED (`math.machine-checked`): with each pair's transport
map taken **measurable** (finding F19 below), the glue is elementary -- carve measurable full-mass
carriers `C i := (toMeasurable (μ₀ i) (S i)ᶜ)ᶜ ⊆ S i` (pairwise disjoint, inherited from `S`, so NO
optimal-transport / measurable-selection theory is needed -- the original "Mathlib lacks it"
justification was too pessimistic for the disjoint-support case) and set `ψ := ∑ i, (C i).indicator Tᵢ`,
which agrees with each `Tᵢ` `μ₀ i`-a.e. (`Measure.map_congr`). The carrier-and-glue construction is
factored out as `exists_measurable_glue` above; this proof is now its application.

**Fidelity (soundness):** the disjoint-supports hypotheses are load-bearing and are the paper's context
(Lemma 5.1 takes the measures from Proposition 3.1 applied to both `μ^i₀` and `μ^i₁`, i.e. already
disentangled into disjoint regions). The original stub omitted them, which makes the statement
**false**: with `μ₀ 0 = μ₀ 1 = δ_a` and targets `μ₁ 0 = δ_b`, `μ₁ 1 = δ_e` (`b ≠ e`) each pair is
matchable (`a ↦ b`, `a ↦ e`) but a single `ψ` would need `ψ a = b` and `ψ a = e` at once.

The earlier conclusion additionally claimed `Function.Bijective ψ`, which is unsatisfiable even
WITH disjoint supports: within one pair an atomless source with a Dirac target is matchable, but no
injection pushes an atomless measure onto an atom (review finding F13). The paper's Lemma 5.1
(p.24) does print "invertible", but its own proof (B.4) composes `ψ^i = T^i_{Φ₃} ∘ T^i ∘
(T^i_{Φ₁})^{-1}` where the per-pair transport `T^i` need not be invertible -- a statement/proof
mismatch recorded as erratum candidate E2 in `ERRATA.md`. The faithful conclusion keeps
measurability (required for the pushforward to be meaningful) and drops invertibility.

**Missing-measurability gap (finding F19, the repair that makes this provable):** the pre-F19 hypothesis
was `hmatch : ∀ i, ∃ Tᵢ, (μ₀ i).map Tᵢ = μ₁ i` with **no measurability on `Tᵢ`**. Mathlib defines
`Measure.map f = 0` when `f` is not `AEMeasurable`, so that hypothesis is satisfiable by a non-measurable
`Tᵢ` with `μ₁ i = 0` while `μ₀ i ≠ 0`; the conclusion then demands a *measurable* `ψ` with
`(μ₀ i).map ψ = 0`, impossible because a measurable pushforward preserves total mass
(`(μ₀ i).map ψ Set.univ = μ₀ i Set.univ ≠ 0`). The unrestricted form is therefore **not provable**. No
constructive kernel refutation exists (exhibiting the gap requires a non-measurable function, which is
non-constructive), so this is recorded as a reasoned soundness note rather than a committed `False`
(`RESEARCH.md` F19). The paper's transport maps are Monge maps -- measurable by construction -- so the
faithful repair is the added `Measurable Tᵢ`, matching the F11-F18 pattern. The target-disjointness
hypothesis (bound `_hdisj₁`) is retained for the paper's disentangled context though this pushforward
direction does not consume it. -/
theorem lemma_5_1 {N : ℕ} (μ₀ μ₁ : Fin N → Measure (Eucl d))
    (hdisj₀ : DisjointSupports μ₀) (_hdisj₁ : DisjointSupports μ₁)
    (hmatch : ∀ i, ∃ Ti : Eucl d → Eucl d, Measurable Ti ∧ (μ₀ i).map Ti = μ₁ i) :
    ∃ ψ : Eucl d → Eucl d, Measurable ψ ∧ ∀ i, (μ₀ i).map ψ = μ₁ i := by
  choose T hTmeas hTmap using hmatch
  obtain ⟨ψ, hψmeas, hψae⟩ := exists_measurable_glue μ₀ hdisj₀ T hTmeas
  exact ⟨ψ, hψmeas, fun i => by rw [Measure.map_congr (hψae i)]; exact hTmap i⟩

/-- **Lemma 5.4** (`L²` approximation by a flow map). Any measurable, a.e. sphere-valued transport
map `ψ` of a sphere-supported probability measure is approximated in `L²(μ)` by a flow map of the
dynamics, to any tolerance, with finitely many switches. **Proved** (`math.machine-checked`):
value rounding (`exists_finite_range_sphere_approx`) replaces `ψ` by a finite-range approximant
`ψ'` at a.e. sup error `ε/2`, the finite-range core (`lemma_5_4_of_finite_range`, the full G8
staging/relocation pipeline over `V = 0` universal-transport-map schedules) realizes `ψ'` to
`L²` error `ε/2` at exact duration `T`, and the raw sqrt-integral triangle inequality
(`sqrtIntegral_sub_le_add`) combines the legs. Combined with the coupling bound (leaf L7) this
controls `W₂`. The approximant `ψε` is measurable and the displacement is `L²`-integrable --
both implicit in the `∫` bound being meaningful, made explicit so the `W₂` map bound
(`W2_map_le_L2`) can consume them.

The flow conjunct is UNIVERSAL: the schedule's blocks are all `V = 0`, so its single transport
map `ψε` pushes forward every sphere-supported probability measure `ν` at once, not just the
input `μ` (the paper's map is "induced by the solution map of (B.1)", i.e. measure-independent;
the value-rounding leg is per-`μ` but only feeds the `L²` estimate, never the transport map).
The input instance is the application at `ν := μ`.

**Fidelity (soundness):** the paper's Lemma 5.4 (p.24, arXiv:2411.04551v3) verbatim: "Suppose
`ε > 0` and `μ ∈ P(S^{d-1})`. For every `ψ ∈ L²(S^{d-1}; S^{d-1})`, there exists a
Lipschitz-continuous and invertible map `ψε : S^{d-1} → S^{d-1}` induced by the solution map of
(B.1), namely `Φ^T_{θε}(μ) = (ψε)#μ` for some piecewise constant `θε : [0,T] → Θ` with finitely
many switches, such that `‖ψ − ψε‖_{L²(μ)} ⩽ ε`." The map is sphere-valued. The original stub
quantified over every measure and every `ψ` and was refutable: flow approximants are sphere-valued
on sphere mass, so `ψ = const (3 • e₁)` on `μ = δ_{e₁}` keeps every approximant at `L²` distance
at least `2` (review finding F12). Sphere-valued `ψ` on sphere-supported `μ` is automatically `L²`.

**Dimension repair (finding F31):** stated dimension-free, the schema is refutable at `d = 1`: on
`S⁰` the tangential projector at a unit point annihilates every vector, so every mean-field flow
freezes sphere Diracs, and `ψ = const (-e)` on `μ = δ_e` keeps every approximant at `L²` distance
exactly `2` -- a compiling proof of `False` (kernel disproof: the F31 regression suite,
`Regression.Refuted`). Repaired with `hd : 3 ≤ d`: the paper's standing scope (Theorem 1.2, p.5,
"Suppose `d ⩾ 3`") and the exact hypothesis its sole consumer `theorem_1_2` already carries; it is
also load-bearing for the planned discharge (the three-pull steering of `ClusterToPoint` consumes
a doubly-orthogonal relay pole).

Layer (F14): mean-field -- the paper's density argument ranges over the full attention dynamics. -/
theorem lemma_5_4 (hd : 3 ≤ d) (μ : Measure (Eucl d)) [IsProbabilityMeasure μ]
    (ψ : Eucl d → Eucl d) (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (hμs : supportedIn μ (sphere d)) (hψm : Measurable ψ)
    (hψs : ∀ᵐ x ∂μ, ψ x ∈ sphere d) :
    ∃ (θ : AttnSchedule d) (ψε : Eucl d → Eucl d),
      AttnSchedule.durationSum θ = T ∧
      (∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] → supportedIn ν (sphere d) →
        attnMeasureFlow θ ν = ν.map ψε) ∧
      Measurable ψε ∧
      Integrable (fun x => ‖ψ x - ψε x‖ ^ 2) μ ∧
      Real.sqrt (∫ x, ‖ψ x - ψε x‖ ^ 2 ∂μ) ≤ ε := by
  -- round `ψ` to a finite on-sphere range at a.e. sup error `ε/2`
  obtain ⟨ψ', s, hs_sphere, hs_range, hψ'm, hψ'close⟩ :=
    Leaves.exists_finite_range_sphere_approx μ ψ hψm hψs (ε / 2) (by positivity)
  -- the finite-range core at tolerance `ε/2`, exact duration `T`
  obtain ⟨θ, ψε, hdur, hflow, hψεm, hint2, hL2⟩ :=
    lemma_5_4_of_finite_range hd μ ψ' T (ε / 2) hT (by positivity) hμs hψ'm
      (ae_of_all _ fun x => hs_sphere _ (hs_range x)) ⟨s, hs_sphere, hs_range⟩
  -- leg 1: the rounding error, in the raw sqrt-integral form
  have hm1 : AEStronglyMeasurable (fun x => ψ x - ψ' x) μ :=
    (hψm.sub hψ'm).aestronglyMeasurable
  have hint1 : Integrable (fun x => ‖ψ x - ψ' x‖ ^ 2) μ :=
    Leaves.integrable_sq_norm_of_ae_bound hm1 hψ'close
  have hL1 : Real.sqrt (∫ x, ‖ψ x - ψ' x‖ ^ 2 ∂μ) ≤ ε / 2 := by
    have h := Leaves.sqrtIntegral_le_of_good_bad (μ := μ) hm1 MeasurableSet.empty
      (δ := ε / 2) (C := ε / 2) (η := 0) (by positivity) (by positivity) (by simp)
      (by filter_upwards [hψ'close] with x hx _; exact hx) hψ'close (by simp)
    calc Real.sqrt (∫ x, ‖ψ x - ψ' x‖ ^ 2 ∂μ)
        ≤ Real.sqrt ((ε / 2) ^ 2 + (ε / 2) ^ 2 * (0 : ℝ≥0∞).toReal) := h
      _ = ε / 2 := by
          rw [ENNReal.toReal_zero, mul_zero, add_zero]
          exact Real.sqrt_sq (by positivity)
  have hm2 : AEStronglyMeasurable (fun x => ψ' x - ψε x) μ :=
    (hψ'm.sub hψεm).aestronglyMeasurable
  refine ⟨θ, ψε, hdur, hflow, hψεm,
    Leaves.integrable_sq_norm_sub_of_legs hm1 hm2 hint1 hint2, ?_⟩
  calc Real.sqrt (∫ x, ‖ψ x - ψε x‖ ^ 2 ∂μ)
      ≤ Real.sqrt (∫ x, ‖ψ x - ψ' x‖ ^ 2 ∂μ)
          + Real.sqrt (∫ x, ‖ψ' x - ψε x‖ ^ 2 ∂μ) :=
        Leaves.sqrtIntegral_sub_le_add hm1 hm2 hint1 hint2
    _ ≤ ε / 2 + ε / 2 := add_le_add hL1 hL2
    _ = ε := by ring

/-- **Lemma B.2** (single ball pair). Mass in the geodesic ball `ℬ₀ = B(z₀, R₀)` is pushed into
`ℬ₀ ∩ ℬ₁` (`ℬ₁ = B(z₁, R₁)`), retaining a `(1-ε)` fraction, with a single parameter switch.

**Proved** (`math.machine-checked`): the M4 discharge. The dynamical core is the amplitude-scaled
ReLU-gated block of Appendix B (review finding F1: the paper's printed gate parameters have the
activation side reversed; the corrected sign is `U = +z 1ᵀ, b = -cos(R) 1`, see `ERRATA.md`),
recentered at a point `ω` of the overlap: the sub-cap of `ℬ₀` carrying the `(1-ε)` fraction
(eq. B.6, `exists_closed_sublevel_mass_ge`) lies in a cap around `ω` by the geodesic triangle
inequality, the self-centered gated flow contracts that cap into `B(ω, r) ⊆ ℬ₀ ∩ ℬ₁`
(`gatedBlock_reach` through `exists_scaledGatedBlock_mapsTo_cap`, the amplitude buying the
log-odds budget at the fixed horizon `T`), and the pushforward bridge
(`Axioms.le_measureFlow_of_mapsTo`) turns the point-set contraction into mass retention. The whole
chain is `Leaves.gated_twoCap_retention`. The `switches θ ≤ 1` bound holds because the schedule is
a single block. The dimension hypothesis `_hd` is no longer load-bearing -- with sub-hemisphere
radii the `d = 1` caps collapse to their centres, which the pole case of the contraction handles --
but is kept for statement stability across the discharge.

**Fidelity (soundness):** the hypotheses are now genuine **geodesic balls** `B(zᵢ, Rᵢ)` with centers
on the sphere, not arbitrary sets. The gated characteristic funnels a *cap* toward its overlap with
another cap; stated for arbitrary `B₀, B₁` the retention claim is false (nothing steers an arbitrary
set into another). This restriction matches Appendix B and is what the eventual discharge (via
`gatedBlock` + the logistic reaching estimate `logistic_flow_reach` + the cap-mass estimate
`exists_closed_sublevel_mass_ge`) will prove.

The dimension and radius bounds are likewise load-bearing (review finding F12): at `d = 1` radial
tangency forces the field to vanish at `±1`, so both sphere points are fixed and no transport
happens at all. The caps are restricted to **sub-hemisphere radii** `R ∈ (0, π/2)`: for the gated
field pushing toward `ω ∈ ℬ₀`, the rim derivative is `d/dt ⟪z₀,x⟫ = gate·(⟪z₀,ω⟫ - ⟪ω,x⟫·⟪z₀,x⟫)
≥ gate·(⟪z₀,ω⟫ - cos R₀) > 0` only because `cos R₀ ≥ 0`; for `R₀ > π/2` a trajectory can stall on
the rim before reaching the overlap, and adversarial mass concentrated near the antipode `-ω`
(which a super-hemisphere cap can contain together with `ω`) defeats any single gate. The
probability hypothesis is equally load-bearing: for an infinite measure stacking mass `c_k → ∞` on
points approaching the rim from inside, any single finite-amplitude block moves the near-rim atoms
too slowly to reach the overlap in time `T`, so the transported mass stays finite while
`(1-ε)·μ(ℬ₀) = ⊤`. The paper has both: `μ₀ ∈ P(S^{d-1})` and small caps (Appendix B chains).

`_hd : 2 ≤ d` is retained for statement fidelity to the paper's ambient dimension, even though the
discharge (`gated_twoCap_retention`) does not need it: the sub-hemisphere-radius and probability
restrictions above are what carry the soundness (the `d = 1` degeneracy is a *different*, non-generic
failure mode this hypothesis would have guarded against had the discharge route needed it). -/
theorem lemma_B_2 (μ : Measure (Eucl d)) [IsProbabilityMeasure μ] (_hd : 2 ≤ d)
    (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (z₀ z₁ : Eucl d) (hz₀ : z₀ ∈ sphere d) (hz₁ : z₁ ∈ sphere d) (R₀ R₁ : ℝ)
    (hR₀ : R₀ ∈ Set.Ioo 0 (Real.pi / 2)) (hR₁ : R₁ ∈ Set.Ioo 0 (Real.pi / 2))
    (hcap : (geodesicBall z₀ R₀ ∩ geodesicBall z₁ R₁).Nonempty) :
    ∃ θ : Params d, switches θ ≤ 1 ∧
      (1 - ENNReal.ofReal ε) * μ (geodesicBall z₀ R₀) ≤
        (measureFlow θ T μ) (geodesicBall z₀ R₀ ∩ geodesicBall z₁ R₁) :=
  MeasureToMeasure.gated_twoCap_retention μ T ε hT hε z₀ z₁ hz₀ hz₁ R₀ R₁ hR₀ hR₁ hcap

/-- **Lemma B.1** (ball-chain retention). For a chain of `K+1` consecutively overlapping balls, `K`
switches retain a `(1-ε)^K` fraction of the mass initially in `ℬ₀` into the last ball `ℬ_K`.

**Proved** (`math.machine-checked`: rests on the proved theorem `lemma_B_2` and the structural flow
algebra, no remaining axiom): a genuine induction on `K`. The base case is the identity schedule (`idParams`); each step composes a
single-ball `lemma_B_2` transport via `comp`, using `measureFlow_comp` to carry the previous mass
forward, `measure_mono` to pass from `ℬ_k ∩ ℬ_{k+1}` to `ℬ_{k+1}`, and `switches_comp` for the budget.

The statement keeps the retained fraction on `μ ℬ₀` (the mass that starts in the first ball,
funneled along the chain) rather than the paper's `μ (⋃ ℬ_k)`. The union form is out of reach here
NOT because of any base-case issue (at `K = 0` the paper's bounded union IS `ℬ₀`, and its base case
is true) but because the Lean `lemma_B_2` drops two clauses the paper's B.1 induction needs for the
union: the localization clause "the flow is the identity on `S^{d-1} ∖ ℬ₀`" and the
`|k - k'| ≥ 2` disjointness hypothesis, which together let mass already sitting in later balls stay
put during earlier legs (review finding F16). The chain-overlap hypothesis `hchain` and the
per-step switch bound (now in `lemma_B_2`) are required for the bound to hold. The chain is a
sequence of genuine **geodesic balls** `B(z_k, R_k)` (centers on the sphere, sub-hemisphere radii)
over a probability measure, matching the faithful `lemma_B_2` signature; the probability instance
is preserved along the chain by `isProbabilityMeasure_measureFlow`. -/
theorem lemma_B_1 (μ : Measure (Eucl d)) [IsProbabilityMeasure μ] (hd : 2 ≤ d)
    (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (K : ℕ) (z : ℕ → Eucl d) (hz : ∀ k, z k ∈ sphere d) (R : ℕ → ℝ)
    (hR : ∀ k, R k ∈ Set.Ioo 0 (Real.pi / 2))
    (hchain : ∀ k, (geodesicBall (z k) (R k) ∩ geodesicBall (z (k + 1)) (R (k + 1))).Nonempty) :
    ∃ θ : Params d, switches θ ≤ K ∧
      (1 - ENNReal.ofReal ε) ^ K * μ (geodesicBall (z 0) (R 0)) ≤
        (measureFlow θ T μ) (geodesicBall (z K) (R K)) := by
  set c : ℝ≥0∞ := 1 - ENNReal.ofReal ε with hc
  induction K with
  | zero =>
    refine ⟨idParams d, ?_, ?_⟩
    · simp [switches_id]
    · simp [measureFlow_id]
  | succ k ih =>
    obtain ⟨θ, hsw, hmass⟩ := ih
    haveI := isProbabilityMeasure_measureFlow θ T μ
    obtain ⟨ψ, hψsw, hψmass⟩ :=
      lemma_B_2 (measureFlow θ T μ) hd T ε hT hε (z k) (z (k + 1)) (hz k) (hz (k + 1))
        (R k) (R (k + 1)) (hR k) (hR (k + 1)) (hchain k)
    refine ⟨comp θ ψ, (switches_comp θ ψ).trans (Nat.add_le_add hsw hψsw), ?_⟩
    rw [measureFlow_comp]
    calc c ^ (k + 1) * μ (geodesicBall (z 0) (R 0))
        = c * (c ^ k * μ (geodesicBall (z 0) (R 0))) := by rw [pow_succ', mul_assoc]
      _ ≤ c * (measureFlow θ T μ) (geodesicBall (z k) (R k)) := by gcongr
      _ ≤ (measureFlow ψ T (measureFlow θ T μ))
            (geodesicBall (z k) (R k) ∩ geodesicBall (z (k + 1)) (R (k + 1))) := hψmass
      _ ≤ (measureFlow ψ T (measureFlow θ T μ)) (geodesicBall (z (k + 1)) (R (k + 1))) :=
          measure_mono Set.inter_subset_right

/-- AXIOM (parking / simultaneous action, Appendix B). If a family of measures has pairwise disjoint
supports and each member can be steered to within `ε` of its target by *some* schedule of at most
`s i` switches, then a *single* schedule of at most `∑ s i` switches steers all of them
simultaneously to within `ε`: each member's schedule is gated to its (disjoint) support region and
parks on the others (`flowMap_id_on_parked`). Mathlib has no continuity-equation theory to derive
this, so it is a labeled structural axiom.

**Source** (Proposition 2.2, pp. 11-12, arXiv:2411.04551v3, whose simultaneous-schedule
conclusion this parking step realizes): "Then for any 𝑇 > 0 and 𝜀 > 0 there exist piecewise
constant (W, U, 𝑏) : [0, 𝑇] → M_{d×d}(ℝ)² × ℝ^d such that for any 𝑖, the corresponding solution
𝜇^𝑖 to (1.3)-(1.2) with data 𝜇₀^𝑖, V ≡ 0 and the above parameters, satisfies
W₂(𝜇^𝑖(𝑇), 𝜇₁^𝑖) ⩽ 𝜀".

**Fidelity (soundness):** the dimension hypothesis is load-bearing (review finding F12): at `d = 1`
every flow map is an increasing homeomorphism of the line, so two Dirac targets cannot be swapped,
and at `d = 2` the cyclic order of the circle gives the same obstruction; the paper's gating
construction needs room to route around parked regions, available from `d ≥ 3`. The switch budget
is the sum of the per-member budgets, matching the gate-and-concatenate construction. The horizon
positivity `hT : 0 < T` is the paper's own quantifier ("for any 𝑇 > 0", above); it was DROPPED in
an earlier form of this axiom, which made the statement inconsistent (finding F33): at `N = 0`
every per-member hypothesis is vacuous, so `T = -1` would produce a schedule of negative total
duration, contradicting `AttnSchedule.durationSum_nonneg`
(`Regression/Refuted/F33_ParkedScheduleNegativeT.lean`). With `hT` the exploit is blocked and the
`N = 0, T > 0` corner is satisfiable (any single block of duration `T` works).

Layer (F14): mean-field -- the parked family members are SEPARATE mean-field systems sharing one
schedule (each `ν i` evolves under its own self-attention field), which is exactly the paper's
family setting. Note this family form does NOT apply to pieces of a single mixture: a mixture
evolves as one system and its flow is not the mixture of its pieces' flows (that distinction is
why `prop_2_2` lives on the linear layer, where its paper construction is). -/
axiom exists_parked_schedule {N : ℕ} (hd : 3 ≤ d) (ν target : Fin N → Measure (Eucl d)) (T ε : ℝ)
    (hT : 0 < T) (s : Fin N → ℕ)
    (hdisj : DisjointSupports ν)
    (hper : ∀ i, ∃ θ : AttnSchedule d, AttnSchedule.durationSum θ = T ∧
      AttnSchedule.switches θ ≤ s i ∧
      Axioms.W2 (attnMeasureFlow θ (ν i)) (target i) ≤ ε) :
    ∃ Θ : AttnSchedule d, AttnSchedule.durationSum Θ = T ∧ AttnSchedule.switches Θ ≤ ∑ i, s i ∧
      ∀ i, Axioms.W2 (attnMeasureFlow Θ (ν i)) (target i) ≤ ε

/-- Atomless decomposition (Sierpiński/Lyapunov splitting). An atomless probability measure splits
into `M` probability measures `P k` with prescribed convex weights `α k` (`∑ α k = 1`, each `α k ≠ 0`)
and pairwise disjoint supports: `μ = ∑ α k • P k`.

**Proved** (`Foundations.exists_probability_decomposition`): the pieces are the normalized restrictions
`P k = (α k)⁻¹ • μ.restrict (A k)` to a prescribed-mass disjoint partition `A k`, which is carved by
iterating **Sierpiński's intermediate-value theorem** for nonatomic measures. The bespoke partition
axiom is thereby removed; what remains is the single primitive
`Foundations.exists_measurableSet_subset_measure_eq` (that IVT, absent from Mathlib `v4.31.0`; Fremlin,
*Measure Theory* Vol. 2, §215D). Positive weights (`α k ≠ 0`) are assumed so each normalized piece is a
genuine probability measure; a zero-weight atom is vacuous for a discrete target.

Soundness note: an earlier form additionally required each piece to sit in an open hemisphere. That
clause is inconsistent at `M = 1` -- it would force the whole measure into a half-space through the
origin, which no centrally-symmetric atomless measure (a Gaussian, or the uniform law on a ball or
sphere) satisfies -- so it is dropped here. The hemisphere is instead acquired dynamically per piece
inside `prop_2_2` (rotate into the orthant via `lemma_3_2`), the way the paper actually proceeds. -/
theorem exists_atomless_partition (μ : Measure (Eucl d)) [IsProbabilityMeasure μ]
    (hatomless : ∀ x : Eucl d, μ {x} = 0)
    {M : ℕ} (α : Fin M → ℝ≥0∞) (hα : ∑ k, α k = 1) (hα0 : ∀ k, α k ≠ 0) :
    ∃ P : Fin M → Measure (Eucl d), (∀ k, IsProbabilityMeasure (P k)) ∧
      μ = ∑ k, α k • P k ∧ DisjointSupports P := by
  haveI : NoAtoms μ := ⟨hatomless⟩
  obtain ⟨P, S, hProb, hμeq, hsupp, hSdisj⟩ :=
    Foundations.exists_probability_decomposition μ α hα hα0
  exact ⟨P, hProb, hμeq, S, hsupp, hSdisj⟩

/-- A piece of a convex decomposition inherits the support of the whole: if `∑ αₖ • Pₖ` is supported in
`S` and every weight is nonzero, each `Pₖ` is supported in `S`. (In `ℝ≥0∞` a sum of nonnegatives
vanishes iff each term does, and `αₖ ≠ 0` cancels.) -/
theorem supportedIn_of_sum_smul {M : ℕ} (α : Fin M → ℝ≥0∞) (P : Fin M → Measure (Eucl d))
    (hα0 : ∀ k, α k ≠ 0) {S : Set (Eucl d)} (h : supportedIn (∑ k, α k • P k) S) (k : Fin M) :
    supportedIn (P k) S := by
  have hsum : ∑ j, α j * P j Sᶜ = 0 := by
    have := h
    simp only [supportedIn, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      smul_eq_mul] at this
    exact this
  have hk : α k * P k Sᶜ = 0 := (Finset.sum_eq_zero_iff.mp hsum) k (Finset.mem_univ k)
  exact (mul_eq_zero.mp hk).resolve_left (hα0 k)

/-- A sphere-supported measure is a.e. bounded in norm by any `R ≥ 1` (on the sphere `‖y‖ = 1`). -/
theorem ae_norm_le_of_supportedIn_sphere {ν : Measure (Eucl d)} {R : ℝ} (hR : 1 ≤ R)
    (h : supportedIn ν (sphere d)) : ∀ᵐ y ∂ν, ‖y‖ ≤ R := by
  rw [ae_iff]
  refine measure_mono_null (fun y hy => ?_) h
  simp only [Set.mem_setOf_eq, not_le] at hy
  simp only [sphere, Set.mem_compl_iff, Metric.mem_sphere, dist_zero_right]
  intro hy1; rw [hy1] at hy; linarith

/-- **Proposition 2.2** (clustering to a discrete measure). An atomless probability measure on the
sphere can be driven `W₂`-close to a prescribed `M`-atom discrete measure `∑ α k • δ_{x k}` on the
sphere (convex weights, `∑ α k = 1`, each `α k ≠ 0`). AXIOM (`math.axiomatised`): the paper's own
proof (Section 2.2 and Remark 2.3) is a GATED PERCEPTRON construction -- prescribed-mass splitting
(machine-checked here as `exists_atomless_partition`) followed by ball-chain transport of each
piece (Lemmas B.1/B.2), all with `V ≡ 0` parameters -- so the statement lives faithfully on the
linear layer. `Depends-On exists_atomless_partition`, `Depends-On lemma_B_1`.

**Assembly status (partial).** The *combination* half of the derivation is now machine-checked:
`Leaves.measureFlow_W2_discrete_of_perPiece` proves that a SINGLE schedule `θ` driving every piece
`W₂`-near its Dirac drives the mixture `W₂`-near `∑ αₖ • δ_{x k}` -- the linear flow's distributivity
(`measureFlow_sum_smul`) composed with mixture-convexity of `W₂` (`W2_convexCombo_le`). This reduces
`prop_2_2` to a single remaining obligation, which is what keeps it axiomatised: the existence of
ONE gated schedule that simultaneously transports each disjoint piece into a small ball around its
prescribed target while PARKING the others. Its per-piece step is `lemma_B_1` (ball-chain mass
concentration), but the honest close additionally needs (i) a prescribed-weight AND geometrically
localized partition (`exists_atomless_partition` carves by mass via Sierpiński, not into caps, so a
full-support datum -- e.g. the uniform law -- is not captured by any single sub-`π/2` ball), and
(ii) the disjoint gating/non-interference that lets the per-piece schedules concatenate without
disturbing one another. Both are the paper's §2.2 mass-sweep (`O(M)` switches, non-explicit constant
§1.4.3), which Mathlib `v4.31.0`'s absent continuity-equation theory cannot yet express -- deferred,
not invented.

History (F14): an earlier machine-checked assembly routed each piece through `lemma_3_2` and the
attention-based `cluster_to_point`, then parked the pieces and used the linearity
`measureFlow Θ (∑ αₖ • Pₖ) = ∑ αₖ • measureFlow Θ (Pₖ)`. That route is valid ONLY in the
measure-independent model: under the mean-field dynamics a mixture evolves as one system, and its
flow is NOT the mixture of its pieces' flows. With `cluster_to_point` restated on the mean-field
layer (where it belongs), the old route is no longer meaningful, and the earlier `MissingCap`
hypothesis (an artifact of the `lemma_3_2` rotation step) and the `9 M` budget (an artifact of the
composite) are dropped; the paper's own switch count for this regime is `O(M)` with a non-explicit
constant (§1.4.3), deferred rather than invented.

**Fidelity (soundness):** probability, atomless, sphere support, and on-sphere targets are the
paper's hypotheses (`μ₀ ∈ P(S^{d-1})` atomless, targets `δ_{x_k}` with `x_k ∈ S^{d-1}`); `d ≥ 3`
matches the ball-chain construction's room requirement (cf. `lemma_B_2`'s `d ≥ 2` plus the
routing/parking obstruction at `d = 2`, finding F12).

**Fidelity fix (F21, 2026-07-12):** the paper's own statement (p.12) additionally requires
`x_k^i ∈ conv_g supp μ_0^i` -- each target lies in the geodesic convex hull of the INPUT's support --
which this axiom had dropped, making it strictly more general than what the paper establishes (a
counterexample-shaped instance: `d ≥ 3`, `μ` concentrated in a tiny cap near `z`, `M = 2` with
`x_1 ≈ z`, `x_2 = -z` antipodal, `α_2 = 0.9` -- no construction keyed to `μ`'s own geometry can
reach `x_2`, since essentially none of `μ`'s mass is anywhere near it). Restored below as `hxhull`,
the intersection-of-closed-convex-supersets characterization of the hull (`∀ s`, CLOSED and
geodesically convex and carrying `μ`'s full mass, `x k ∈ s`) -- equivalent to (closed) hull
membership since `GeodesicConvex` is closed under arbitrary intersection (`geodesicConvex_iInter`)
and closedness is too, so this needs no new hull operator. The `IsClosed` conjunct matters: without
it, a set can drop individual `μ`-null boundary points of `supp μ` (e.g. an arc minus one endpoint)
and stay geodesically convex while still carrying full mass, making the bare measure-only form
subtly STRONGER than the paper's hull (excludes points that ARE in `supp μ`) rather than equal to
it; requiring `IsClosed` recovers exactly `⋂ {closed convex s | s ⊇ supp μ}` (closed + full-measure
⟺ `⊇ supp μ`, by minimality of the topological support among closed full-measure sets), the standard
closed convex hull of a closed generating set. This is NOT a repeat of the per-piece open-hemisphere
clause finding F12 removed from `exists_atomless_partition`/`prop_2_2` (inconsistent at `M = 1`: it
forced the WHOLE support into a half-space, false for any centrally-symmetric `μ` -- see "Fidelity
corrections made while closing" in `RESEARCH.md`): a blanket hemisphere hypothesis can be outright
FALSE for such `μ`, whereas `hxhull`'s universal-over-supersets form instead DEGENERATES to no
constraint (vacuously true, not False) exactly when `supp μ` admits no proper closed geodesically-
convex cover -- it cannot reproduce that inconsistency. No constructive kernel refutation of the
pre-fix axiom is recorded (witnessing it would require exhibiting, for the counterexample instance
above, that NO piecewise-constant schedule of ANY length reaches `ε`-closeness -- a
universally-quantified non-existence claim, non-constructive in Lean); this is a fidelity tightening
in the sense of F19/F20, not a `Regression/Refuted/` disproof. The axiom remains `math.axiomatised`;
`hxhull` is additive (no downstream caller in this codebase). -/
axiom prop_2_2 (μ : Measure (Eucl d)) [IsProbabilityMeasure μ] (hd : 3 ≤ d)
    (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (hatomless : ∀ x : Eucl d, μ {x} = 0)
    (hμsupp : supportedIn μ (sphere d))
    (M : ℕ) (x : Fin M → Eucl d) (hx : ∀ k, x k ∈ sphere d)
    (hxhull : ∀ k, ∀ s : Set (Eucl d), IsClosed s → GeodesicConvex s → supportedIn μ s → x k ∈ s)
    (α : Fin M → ℝ≥0∞) (hα : ∑ k, α k = 1)
    (hα0 : ∀ k, α k ≠ 0)
    (ν_target : Measure (Eucl d))
    (htgt : ν_target = ∑ k : Fin M, α k • Measure.dirac (x k)) :
    ∃ θ : Params d, Axioms.W2 (measureFlow θ T μ) ν_target ≤ ε

end MeasureToMeasure.Statements
