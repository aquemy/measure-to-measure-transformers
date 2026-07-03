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

/-- Each input/target pair is matchable by some *measurable, a.e. sphere-valued* transport map (the
minimal assumption of Theorem 1.2). Measurability is part of "transport map" and is needed for the
pushforward to be the target rather than the zero measure; the sphere-valued clause is the paper's
`T^i : S^{d-1} → S^{d-1}` (data (D), p.3), required because flow maps keep sphere mass on the
sphere, so off-sphere targets are unreachable. -/
def Matchable {N : ℕ} (μ₀ μ₁ : Fin N → Measure (Eucl d)) : Prop :=
  ∀ i, ∃ T : Eucl d → Eucl d, Measurable T ∧ (∀ᵐ x ∂(μ₀ i), T x ∈ sphere d) ∧
    (μ₀ i).map T = μ₁ i

/-- AXIOM (geometric output of the disentanglement dynamics, Section 3.3). Under a shared missing
direction, one schedule concentrates each measure of the family into a small ball
`B(α i, r)` (`r < 1`) around a *unit* direction `α i`, with the directions pairwise separated by at
least `2 r`. This is exactly what Lemmas 3.2 (rotate into the orthant), 3.3 (shrink each hull onto its
barycenter direction) and 3.4 (make barycenter directions pairwise non-colinear) produce, run as the
Section 3.3 induction; the leaf L11 (`barycenter_noncolinear_of_disjoint_hull`) is the geometric core.
The dynamical construction rests on the missing continuity-equation theory, so it is axiomatized at
this concrete geometric level. `Depends-On` Lemmas 3.2-3.4 and leaf L11. -/
axiom exists_disentangling_balls (hd : 3 ≤ d) {N : ℕ} (μ₀ : Fin N → Measure (Eucl d))
    (T : ℝ) (hT : 0 < T) (hmiss : SharedMissingDirection μ₀) :
    ∃ (θ : Params d) (α : Fin N → Eucl d) (r : ℝ), 0 < r ∧ r < 1 ∧
      (∀ i, ‖α i‖ = 1) ∧
      (∀ i j, i ≠ j → 2 * r ≤ dist (α i) (α j)) ∧
      (∀ i, supportedIn (measureFlow θ T (μ₀ i)) (Metric.ball (α i) r))

/-- **Proposition 3.1** (disentanglement). Under a shared missing direction there is a schedule whose
solution map renders the family's supports pairwise disjoint, each concentrated in an open
hemisphere.

**Proved** (effective `math.axiomatised`): the dynamical construction is captured by
`exists_disentangling_balls` (the concrete output of Lemmas 3.2-3.4), and this proof discharges the
geometric packaging the paper states without proof (review finding F2): from balls around unit
directions separated by `2 r` we machine-check that (i) the carrier balls are pairwise *disjoint*
(`Metric.ball_disjoint_ball`), and (ii) each ball lies in the open hemisphere `{x | 0 < ⟪α i, x⟫}`
(Cauchy-Schwarz: `‖x - α i‖ < r < 1` forces `⟪α i, x⟫ > 1 - r > 0`). -/
theorem prop_3_1 (hd : 3 ≤ d) {N : ℕ} (μ₀ : Fin N → Measure (Eucl d)) (T : ℝ) (hT : 0 < T)
    (hmiss : SharedMissingDirection μ₀) :
    ∃ θ : Params d, DisjointSupports (fun i => measureFlow θ T (μ₀ i)) ∧
      ∀ i, ∃ e : Eucl d, ‖e‖ = 1 ∧ supportedIn (measureFlow θ T (μ₀ i)) {x | 0 < ⟪e, x⟫} := by
  obtain ⟨θ, α, r, hr0, hr1, hα, hsep, hsupp⟩ := exists_disentangling_balls hd μ₀ T hT hmiss
  -- Each carrier ball lies in the open hemisphere around its centre direction.
  have hball_hemi : ∀ (i : Fin N) (x : Eucl d), x ∈ Metric.ball (α i) r → 0 < ⟪α i, x⟫ := by
    intro i x hx
    rw [Metric.mem_ball] at hx
    have hnorm : ‖x - α i‖ < r := by rw [← dist_eq_norm]; exact hx
    have hself : ⟪α i, α i⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, hα i]; norm_num
    have hbound : -‖x - α i‖ ≤ ⟪α i, x - α i⟫ := by
      have habs := abs_real_inner_le_norm (α i) (x - α i)
      rw [hα i, one_mul] at habs
      have := (abs_le.mp habs).1
      linarith
    have hexp : ⟪α i, x⟫ = ⟪α i, x - α i⟫ + ⟪α i, α i⟫ := by
      rw [inner_sub_right]; ring
    rw [hexp, hself]
    linarith
  refine ⟨θ, ⟨fun i => Metric.ball (α i) r, hsupp, ?_⟩, ?_⟩
  · -- The carrier balls are pairwise disjoint because their centres are `2r`-separated.
    intro i j hij
    exact Metric.ball_disjoint_ball (by linarith [hsep i j hij])
  · -- Each measure is supported in the hemisphere around its centre direction.
    intro i
    refine ⟨α i, hα i, ?_⟩
    have hsub : Metric.ball (α i) r ⊆ {x | 0 < ⟪α i, x⟫} := fun x hx => hball_hemi i x hx
    exact measure_mono_null (Set.compl_subset_compl.mpr hsub) (hsupp i)

/-- **Theorem 1.1** (Dirac targets). If the inputs share a missing direction, then for any horizon and
tolerance a single piecewise-constant `θ` steers each input to within `ε` of its point-mass target
`δ_{x i}` in `W₂`.

**Proved** by assembly: disentangle the family (`prop_3_1`), cluster each disentangled measure to its
target point in its hemisphere (`cluster_to_point`), combine the per-member schedules into one with
the parking construction (`exists_parked_schedule`), and pre-compose with the disentangler
(`comp`, `measureFlow_comp`). Effective status `math.axiomatised`.

The sphere-supported inputs and on-sphere targets are the paper's data (D) (`μ₀^i ∈ P(S^{d-1})`,
`x^i ∈ S^{d-1}`); they thread the repaired `cluster_to_point` (F12). -/
theorem theorem_1_1 (hd : 3 ≤ d) {N : ℕ} (μ₀ : Fin N → Measure (Eucl d)) (x : Fin N → Eucl d)
    (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε) (hmiss : SharedMissingDirection μ₀)
    (hμ : ∀ i, IsProbabilityMeasure (μ₀ i))
    (hμs : ∀ i, supportedIn (μ₀ i) (sphere d)) (hx : ∀ i, x i ∈ sphere d) :
    ∃ θ : Params d, ∀ i, Axioms.W2 (measureFlow θ T (μ₀ i)) (Measure.dirac (x i)) ≤ ε := by
  obtain ⟨θ₁, hdisj, hhemi⟩ := prop_3_1 hd μ₀ T hT hmiss
  -- Each disentangled measure can be clustered to its prescribed target point (7 pieces).
  have hper : ∀ i, ∃ θ : Params d, switches θ ≤ 7 ∧
      Axioms.W2 (measureFlow θ T (measureFlow θ₁ T (μ₀ i))) (Measure.dirac (x i)) ≤ ε := by
    intro i
    obtain ⟨e, he, hsupp⟩ := hhemi i
    haveI := hμ i
    haveI := isProbabilityMeasure_measureFlow θ₁ T (μ₀ i)
    exact cluster_to_point (measureFlow θ₁ T (μ₀ i)) hd T ε hT hε (x i) e (hx i) he
      (measureFlow_supportedIn_sphere θ₁ hT.le (hμs i)) hsupp
  -- Park the per-member schedules into a single schedule acting on the disjoint family.
  obtain ⟨Θ, _hΘsw, hΘ⟩ :=
    exists_parked_schedule hd (fun i => measureFlow θ₁ T (μ₀ i)) (fun i => Measure.dirac (x i))
      T ε (fun _ => 7) hdisj hper
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
machine-checked.

The probability and sphere-support hypotheses on the inputs are the paper's data (D); they feed the
repaired `lemma_5_4` (F12), whose a.e. sphere-valued transport requirement is met through the new
sphere-valued clause of `Matchable` pulled back along the inverse flow. -/
theorem theorem_1_2 (hd : 3 ≤ d) {N : ℕ} (μ₀ μ₁ : Fin N → Measure (Eucl d))
    (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (hmiss₀ : SharedMissingDirection μ₀) (_hmiss₁ : SharedMissingDirection μ₁)
    (hμ : ∀ i, IsProbabilityMeasure (μ₀ i))
    (hμ₀s : ∀ i, supportedIn (μ₀ i) (sphere d))
    (hmatch : Matchable μ₀ μ₁) :
    ∃ θ : Params d, ∀ i, Axioms.W2 (measureFlow θ T (μ₀ i)) (μ₁ i) ≤ ε := by
  obtain ⟨θ₁, hdisj, _⟩ := prop_3_1 hd μ₀ T hT hmiss₀
  have hper : ∀ i, ∃ θ : Params d,
      Axioms.W2 (measureFlow θ T (measureFlow θ₁ T (μ₀ i))) (μ₁ i) ≤ ε := by
    intro i
    obtain ⟨Ti, hTim, hTis, hTi⟩ := hmatch i
    haveI := hμ i
    haveI : IsProbabilityMeasure (measureFlow θ₁ T (μ₀ i)) :=
      isProbabilityMeasure_measureFlow θ₁ T (μ₀ i)
    set ν : Measure (Eucl d) := measureFlow θ₁ T (μ₀ i) with hν
    have hνs : supportedIn ν (sphere d) :=
      measureFlow_supportedIn_sphere θ₁ hT.le (hμ₀s i)
    -- ν is matchable to μ₁ i via S = Ti ∘ (Φ_{θ₁}⁻¹).
    set S : Eucl d → Eucl d := Ti ∘ flowMap (inv θ₁) T with hS
    have hSmeas : Measurable S := hTim.comp (measurable_flowMap (inv θ₁) hT.le)
    have hmap : ν.map S = μ₁ i := by
      rw [hS, ← Measure.map_map hTim (flowMap_measurable (inv θ₁) T), ← measureFlow_map,
        hν, measureFlow_inv]
      exact hTi
    -- S is a.e. sphere-valued on ν: pull the a.e. statement back through the pushforward and
    -- cancel the flow with its reverse-and-negate inverse.
    have hSs : ∀ᵐ y ∂ν, S y ∈ sphere d := by
      have hmeas : MeasurableSet {y : Eucl d | S y ∈ sphere d} :=
        hSmeas Metric.isClosed_sphere.measurableSet
      rw [hν]
      show ∀ᵐ y ∂((μ₀ i).map (flowMap θ₁ T)), S y ∈ sphere d
      rw [MeasureTheory.ae_map_iff (flowMap_measurable θ₁ T).aemeasurable hmeas]
      filter_upwards [hTis] with w hw
      have hinv : flowMap (inv θ₁) T (flowMap θ₁ T w) = w := congrFun (flowMap_inv θ₁ T) w
      simpa [hS, Function.comp_apply, hinv] using hw
    obtain ⟨θ₂, ψε, hflow, hψεmeas, hint, hL2⟩ := lemma_5_4 ν S T ε hT hε hνs hSmeas hSs
    have hfe : (fun x => ‖S x - ψε x‖ ^ 2) = (fun x => ‖ψε x - S x‖ ^ 2) := by
      funext x; rw [norm_sub_rev]
    have hint' : Integrable (fun x => ‖ψε x - S x‖ ^ 2) ν := hfe ▸ hint
    refine ⟨θ₂, ?_⟩
    rw [hflow, ← hmap]
    calc Axioms.W2 (ν.map ψε) (ν.map S)
        ≤ Real.sqrt (∫ x, ‖ψε x - S x‖ ^ 2 ∂ν) := W2_map_le_L2 ν ψε S hψεmeas hSmeas hint'
      _ = Real.sqrt (∫ x, ‖S x - ψε x‖ ^ 2 ∂ν) := by simp_rw [norm_sub_rev]
      _ ≤ ε := hL2
  -- Extract the per-member schedules to obtain explicit switch budgets for the parking axiom
  -- (Lemma 5.4 states no bound, so each member's budget is its own schedule's count).
  choose θs hθs using hper
  obtain ⟨Θ, _hΘsw, hΘ⟩ :=
    exists_parked_schedule hd (fun i => measureFlow θ₁ T (μ₀ i)) μ₁ T ε
      (fun i => switches (θs i)) hdisj (fun i => ⟨θs i, le_rfl, hθs i⟩)
  refine ⟨comp θ₁ Θ, fun i => ?_⟩
  rw [measureFlow_comp]
  exact hΘ i

end MeasureToMeasure.Statements
