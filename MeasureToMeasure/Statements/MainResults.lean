import MeasureToMeasure.Axioms.Wasserstein
import MeasureToMeasure.Axioms.ContinuityEquation
import MeasureToMeasure.Axioms.Dynamics
import MeasureToMeasure.Statements.MidLevel

/-!
# Blueprint statements: the main results (Theorems 1.1 and 1.2) and disentanglement (Prop 3.1)

These are the headline targets of the paper. **Theorems 1.1 and 1.2 are proved here by assembly**:
their proofs combine the mid-level results (`Statements/MidLevel.lean`) and the structural flow
algebra (`Axioms/Dynamics.lean`) along the paper's construction
`Φ_fin = (Φ_θ₁)⁻¹ ∘ Φ_θ₂ ∘ Φ_θ₁` (disentangle, act, re-compose), so the kernel verifies the logical
skeleton. Their effective CKC status is therefore `math.axiomatised` (the minimum over the documented
axiom surface they rest on), *not* `math.open`.

The hypotheses of the paper are now **concrete definitions** (a shared missing direction; pairwise
matchability by a *measurable* transport map; pairwise disjoint supports), so the proofs genuinely
consume and produce them.

`prop_3_1` (disentanglement) is stated as a faithful **axiom**: its honest proof is the Section 3.3
induction that produces explicit pairwise-disjoint supports from Lemmas 3.2-3.4 and the
non-colinearity leaf L11, a large standalone formalization. The two main theorems are assembled over
it. Two structural composition mechanisms the paper uses but Mathlib cannot supply are likewise
labeled axioms: `exists_parked_schedule` (one schedule acting on a disjoint-support family, the
Appendix B parking construction) and `cluster_to_point` (single-measure controllability, in
`MidLevel.lean`).
-/

namespace MeasureToMeasure.Statements

open MeasureTheory MeasureToMeasure.Axioms
open scoped RealInnerProductSpace

variable {d : ℕ}

/-- There is a unit direction `ω` off the (closed) support of every measure in the family
(eq. 1.4-1.5): no measure charges the point `ω` itself, encoded as full mass on `{x | ⟪ω, x⟫ < 1}`. -/
def SharedMissingDirection {N : ℕ} (μ : Fin N → Measure (Eucl d)) : Prop :=
  ∃ ω : Eucl d, ‖ω‖ = 1 ∧ ∀ i, supportedIn (μ i) {x | ⟪ω, x⟫ < 1}

/-- Each input/target pair is matchable by some *measurable* transport map (the minimal assumption of
Theorem 1.2). Measurability is part of "transport map" and is needed for the pushforward to be the
target rather than the zero measure. -/
def Matchable {N : ℕ} (μ₀ μ₁ : Fin N → Measure (Eucl d)) : Prop :=
  ∀ i, ∃ T : Eucl d → Eucl d, Measurable T ∧ (μ₀ i).map T = μ₁ i

/-- The measures in the family have pairwise disjoint supports: a family of carrier sets `S i` (each
holding the full mass of `ν i`) that are pairwise disjoint. -/
def DisjointSupports {N : ℕ} (ν : Fin N → Measure (Eucl d)) : Prop :=
  ∃ S : Fin N → Set (Eucl d), (∀ i, supportedIn (ν i) (S i)) ∧
    Pairwise (fun i j => Disjoint (S i) (S j))

/-- AXIOM (parking / simultaneous action, Appendix B). If a family of measures has pairwise disjoint
supports and each member can be steered to within `ε` of its target by *some* schedule, then a
*single* schedule steers all of them simultaneously to within `ε`: each member's schedule is gated to
its (disjoint) support region and parks on the others (`flowMap_id_on_parked`). Mathlib has no
continuity-equation theory to derive this, so it is a labeled structural axiom. -/
axiom exists_parked_schedule {N : ℕ} (ν target : Fin N → Measure (Eucl d)) (T ε : ℝ)
    (hdisj : DisjointSupports ν)
    (hper : ∀ i, ∃ θ : Params d, W2 (measureFlow θ T (ν i)) (target i) ≤ ε) :
    ∃ Θ : Params d, ∀ i, W2 (measureFlow Θ T (ν i)) (target i) ≤ ε

/-- **Proposition 3.1** (disentanglement). Under a shared missing direction there is a schedule whose
solution map renders the family's supports pairwise disjoint, each concentrated in an open
hemisphere. AXIOM (`math.axiomatised`): the Section 3.3 induction (Lemmas 3.2-3.4, leaf L11) produces
explicit disjoint supports; formalizing that construction is a large standalone task. The hemisphere
clause records that disentanglement also confines each measure to a hemisphere (it rotates them into
the orthant), which the clustering step of Theorem 1.1 consumes. `Depends-On` Lemmas 3.2-3.4. -/
axiom prop_3_1 (hd : 3 ≤ d) {N : ℕ} (μ₀ : Fin N → Measure (Eucl d)) (T : ℝ) (hT : 0 < T)
    (hmiss : SharedMissingDirection μ₀) :
    ∃ θ : Params d, DisjointSupports (fun i => measureFlow θ T (μ₀ i)) ∧
      ∀ i, ∃ e : Eucl d, ‖e‖ = 1 ∧ supportedIn (measureFlow θ T (μ₀ i)) {x | 0 < ⟪e, x⟫}

/-- **Theorem 1.1** (Dirac targets). If the inputs share a missing direction, then for any horizon and
tolerance a single piecewise-constant `θ` steers each input to within `ε` of its point-mass target
`δ_{x i}` in `W₂`.

**Proved** by assembly: disentangle the family (`prop_3_1`), cluster each disentangled measure to its
target point in its hemisphere (`cluster_to_point`), combine the per-member schedules into one with
the parking construction (`exists_parked_schedule`), and pre-compose with the disentangler
(`comp`, `measureFlow_comp`). Effective status `math.axiomatised`. -/
theorem theorem_1_1 (hd : 3 ≤ d) {N : ℕ} (μ₀ : Fin N → Measure (Eucl d)) (x : Fin N → Eucl d)
    (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε) (hmiss : SharedMissingDirection μ₀) :
    ∃ θ : Params d, ∀ i, W2 (measureFlow θ T (μ₀ i)) (Measure.dirac (x i)) ≤ ε := by
  obtain ⟨θ₁, hdisj, hhemi⟩ := prop_3_1 hd μ₀ T hT hmiss
  -- Each disentangled measure can be clustered to its prescribed target point.
  have hper : ∀ i, ∃ θ : Params d,
      W2 (measureFlow θ T (measureFlow θ₁ T (μ₀ i))) (Measure.dirac (x i)) ≤ ε := by
    intro i
    obtain ⟨e, he, hsupp⟩ := hhemi i
    exact cluster_to_point (measureFlow θ₁ T (μ₀ i)) T ε hT hε (x i) e he hsupp
  -- Park the per-member schedules into a single schedule acting on the disjoint family.
  obtain ⟨Θ, hΘ⟩ :=
    exists_parked_schedule (fun i => measureFlow θ₁ T (μ₀ i)) (fun i => Measure.dirac (x i))
      T ε hdisj hper
  refine ⟨comp θ₁ Θ, fun i => ?_⟩
  rw [measureFlow_comp]
  exact hΘ i

/-- **Theorem 1.2** (general targets). If every input/target pair is matchable by a (measurable)
transport map and the inputs share a missing direction, then a single piecewise-constant `θ` steers
each input to within `ε` of its target in `W₂`.

**Proved** by assembly: disentangle the inputs (`prop_3_1`); each disentangled measure `ν₀ i` is then
matchable to `μ₁ i` by `Ti ∘ (Φ_{θ₁}⁻¹)` (using `measureFlow_inv`/`measureFlow_map`); approximate that
transport map by a flow (`lemma_5_4`) and bound `W₂` by the `L²` map distance (the coupling axiom L7,
`W2_map_le_L2`); finally park the per-member schedules into one (`exists_parked_schedule`) and
pre-compose with the disentangler. Effective status `math.axiomatised`; the `W₂` bookkeeping is
machine-checked. -/
theorem theorem_1_2 (hd : 3 ≤ d) {N : ℕ} (μ₀ μ₁ : Fin N → Measure (Eucl d))
    (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (hmiss₀ : SharedMissingDirection μ₀) (_hmiss₁ : SharedMissingDirection μ₁)
    (hmatch : Matchable μ₀ μ₁) :
    ∃ θ : Params d, ∀ i, W2 (measureFlow θ T (μ₀ i)) (μ₁ i) ≤ ε := by
  obtain ⟨θ₁, hdisj, _⟩ := prop_3_1 hd μ₀ T hT hmiss₀
  have hper : ∀ i, ∃ θ : Params d,
      W2 (measureFlow θ T (measureFlow θ₁ T (μ₀ i))) (μ₁ i) ≤ ε := by
    intro i
    obtain ⟨Ti, hTim, hTi⟩ := hmatch i
    set ν : Measure (Eucl d) := measureFlow θ₁ T (μ₀ i) with hν
    -- ν is matchable to μ₁ i via S = Ti ∘ (Φ_{θ₁}⁻¹).
    set S : Eucl d → Eucl d := Ti ∘ flowMap (inv θ₁) T with hS
    have hmap : ν.map S = μ₁ i := by
      rw [hS, ← Measure.map_map hTim (flowMap_measurable (inv θ₁) T), ← measureFlow_map,
        hν, measureFlow_inv]
      exact hTi
    obtain ⟨θ₂, ψε, hflow, hL2⟩ := lemma_5_4 ν S T ε hT hε
    refine ⟨θ₂, ?_⟩
    rw [hflow, ← hmap]
    calc W2 (ν.map ψε) (ν.map S)
        ≤ Real.sqrt (∫ x, ‖ψε x - S x‖ ^ 2 ∂ν) := W2_map_le_L2 ν ψε S
      _ = Real.sqrt (∫ x, ‖S x - ψε x‖ ^ 2 ∂ν) := by simp_rw [norm_sub_rev]
      _ ≤ ε := hL2
  obtain ⟨Θ, hΘ⟩ :=
    exists_parked_schedule (fun i => measureFlow θ₁ T (μ₀ i)) μ₁ T ε hdisj hper
  refine ⟨comp θ₁ Θ, fun i => ?_⟩
  rw [measureFlow_comp]
  exact hΘ i

end MeasureToMeasure.Statements
