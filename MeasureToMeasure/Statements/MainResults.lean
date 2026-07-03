import MeasureToMeasure.Axioms.Wasserstein
import MeasureToMeasure.Axioms.ContinuityEquation
import MeasureToMeasure.Axioms.Dynamics
import MeasureToMeasure.Statements.MidLevel

/-!
# Blueprint statements: the main results (Theorems 1.1 and 1.2) and disentanglement (Prop 3.1)

These are the headline targets of the paper. **Theorems 1.1 and 1.2 are proved here by assembly**:
their proofs combine the mid-level results (`Statements/MidLevel.lean`) and the mean-field schedule
algebra (`Foundations/Attention.lean`) along the paper's construction (disentangle, then act,
running the family as separate mean-field systems sharing one schedule), so the kernel verifies
the logical skeleton. Their effective CKC status is therefore `math.axiomatised` (the minimum over
the documented axiom surface they rest on), *not* `math.open`.

Everything family-level here lives on the MEAN-FIELD layer (`AttnSchedule d` /
`attnMeasureFlow`, finding F14): the paper's eq. (1.7) shows a measure-independent flow cannot
disentangle overlapping inputs (two identical inputs can never enter disjoint balls under one
pushforward map), and the pre-restatement axiom was kernel-refuted exactly that way. The
`Pairwise (μ₀ i ≠ μ₀ j)` hypothesis is the paper's standing assumption (p. 5).

The hypotheses of the paper are **concrete definitions**: a shared missing direction *with a
positive cap gap* (the faithful (1.4)/(1.5) -- the closed supports of the family avoid an open
cap, not merely the point `ω`); pairwise matchability by a measurable, a.e. sphere-valued
transport map; pairwise disjoint supports.

`prop_3_1` (disentanglement) is proved from the faithful axiom `exists_disentangling_balls`, whose
honest derivation is the Section 3.3 induction over Lemmas 3.2-3.4 and the non-colinearity leaf
L11. Its conclusion also exposes the per-member flow maps and their on-sphere inverses (the
paper's Lipschitz-invertible `φ^t`, eq. (B.2)) -- each family member evolves under its OWN
mean-field system, so the maps are per-member. Two structural composition mechanisms the paper
uses but Mathlib cannot supply are likewise labeled axioms: `exists_parked_schedule` and
`cluster_to_point` (in `MidLevel.lean`).

Switch budgets: the paper's `O(d·N)` disentanglement count has a non-explicit constant, so the
budget clauses of `exists_disentangling_balls`, `theorem_1_1`, and `theorem_1_2` are deliberately
deferred rather than invented (quantitative fidelity only where the paper is explicit).
-/

namespace MeasureToMeasure.Statements

open MeasureTheory MeasureToMeasure.Axioms
open MeasureToMeasure.Foundations (AttnSchedule attnMeasureFlow)
open scoped RealInnerProductSpace

variable {d : ℕ}

/-- There is a unit direction `ω` missed by every measure in the family *with a positive cap gap*
`δ`: full mass on `{x | ⟪ω, x⟫ ≤ 1 - δ}` (eq. 1.4-1.5). This is the faithful encoding of
`w₀ ∉ ⋃ᵢ supp(μ₀^i)`: supports are closed, so avoiding `ω` leaves a mass-free open cap.

**Fidelity (soundness):** the earlier encoding (`full mass on {⟪ω, x⟫ < 1}`) only forbade an atom
AT `ω` -- every atomless family satisfied it for every `ω` -- and made `exists_disentangling_balls`
kernel-refutable via a measure with atoms dense in the sphere minus a point (review finding F12/F14
apparatus). The gap form restores the paper's actual strength. -/
def SharedMissingDirection {N : ℕ} (μ : Fin N → Measure (Eucl d)) : Prop :=
  ∃ ω : Eucl d, ‖ω‖ = 1 ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ i, supportedIn (μ i) {x | ⟪ω, x⟫ ≤ 1 - δ}

/-- Each input/target pair is matchable by some *measurable, a.e. sphere-valued* transport map (the
minimal assumption of Theorem 1.2). Measurability is part of "transport map" and is needed for the
pushforward to be the target rather than the zero measure; the sphere-valued clause is the paper's
`T^i : S^{d-1} → S^{d-1}` (data (D), p.3), required because flow maps keep sphere mass on the
sphere, so off-sphere targets are unreachable. -/
def Matchable {N : ℕ} (μ₀ μ₁ : Fin N → Measure (Eucl d)) : Prop :=
  ∀ i, ∃ T : Eucl d → Eucl d, Measurable T ∧ (∀ᵐ x ∂(μ₀ i), T x ∈ sphere d) ∧
    (μ₀ i).map T = μ₁ i

/-- AXIOM (geometric output of the disentanglement dynamics, Section 3.3). Under a shared missing
direction (with its cap gap), one mean-field schedule concentrates each measure of the family into
a small ball `B(α i, r)` (`r < 1`) around a *unit* direction `α i`, with the directions pairwise
separated by at least `2 r`; moreover each member's evolution is realized by a measurable flow map
with a measurable on-sphere inverse (the paper's Lipschitz-invertible `φ^t`, eq. (B.2)) -- the
maps are PER MEMBER because each `μ₀ i` evolves under its own self-attention field. This is
exactly what Lemmas 3.2 (rotate into the orthant), 3.3 (shrink each hull onto its barycenter
direction) and 3.4 (make barycenter directions pairwise non-colinear) produce, run as the Section
3.3 induction; the leaf L11 (`barycenter_noncolinear_of_disjoint_hull`) is the geometric core.
The dynamical construction rests on the missing mean-field theory, so it is axiomatized at this
concrete geometric level. `Depends-On` Lemmas 3.2-3.4 and leaf L11.

**Fidelity (soundness, F14):** stated on the mean-field layer -- the paper's eq. (1.7) proves NO
measure-independent flow can disentangle overlapping inputs, and the pre-restatement linear form
was kernel-refuted (two identical Dirac inputs cannot enter two disjoint balls under one
pushforward). The probability/sphere hypotheses are data (D); `Pairwise (μ₀ i ≠ μ₀ j)` is the
paper's standing assumption (p. 5) -- with equal members even the mean-field flow produces equal
outputs. The switch budget (`O(d·N)`, non-explicit constant) is deliberately deferred. -/
axiom exists_disentangling_balls (hd : 3 ≤ d) {N : ℕ} (μ₀ : Fin N → Measure (Eucl d))
    (T : ℝ) (hT : 0 < T)
    (hμ : ∀ i, IsProbabilityMeasure (μ₀ i))
    (hμs : ∀ i, supportedIn (μ₀ i) (sphere d))
    (hne : Pairwise fun i j => μ₀ i ≠ μ₀ j)
    (hmiss : SharedMissingDirection μ₀) :
    ∃ (θ : AttnSchedule d) (α : Fin N → Eucl d) (r : ℝ),
      AttnSchedule.durationSum θ = T ∧
      0 < r ∧ r < 1 ∧
      (∀ i, ‖α i‖ = 1) ∧
      (∀ i j, i ≠ j → 2 * r ≤ dist (α i) (α j)) ∧
      (∀ i, supportedIn (attnMeasureFlow θ (μ₀ i)) (Metric.ball (α i) r)) ∧
      (∀ i, ∃ Φ Φinv : Eucl d → Eucl d, Measurable Φ ∧ Measurable Φinv ∧
        attnMeasureFlow θ (μ₀ i) = (μ₀ i).map Φ ∧
        ∀ x ∈ sphere d, Φinv (Φ x) = x)

/-- **Proposition 3.1** (disentanglement). Under a shared missing direction there is a schedule whose
solution map renders the family's supports pairwise disjoint, each concentrated in an open
hemisphere.

**Proved** (effective `math.axiomatised`): the dynamical construction is captured by
`exists_disentangling_balls` (the concrete output of Lemmas 3.2-3.4), and this proof discharges the
geometric packaging the paper states without proof (review finding F2): from balls around unit
directions separated by `2 r` we machine-check that (i) the carrier balls are pairwise *disjoint*
(`Metric.ball_disjoint_ball`), and (ii) each ball lies in the open hemisphere `{x | 0 < ⟪α i, x⟫}`
(Cauchy-Schwarz: `‖x - α i‖ < r < 1` forces `⟪α i, x⟫ > 1 - r > 0`). Mean-field layer (F14). -/
theorem prop_3_1 (hd : 3 ≤ d) {N : ℕ} (μ₀ : Fin N → Measure (Eucl d)) (T : ℝ) (hT : 0 < T)
    (hμ : ∀ i, IsProbabilityMeasure (μ₀ i))
    (hμs : ∀ i, supportedIn (μ₀ i) (sphere d))
    (hne : Pairwise fun i j => μ₀ i ≠ μ₀ j)
    (hmiss : SharedMissingDirection μ₀) :
    ∃ θ : AttnSchedule d, AttnSchedule.durationSum θ = T ∧
      DisjointSupports (fun i => attnMeasureFlow θ (μ₀ i)) ∧
      ∀ i, ∃ e : Eucl d, ‖e‖ = 1 ∧ supportedIn (attnMeasureFlow θ (μ₀ i)) {x | 0 < ⟪e, x⟫} := by
  obtain ⟨θ, α, r, hdur, hr0, hr1, hα, hsep, hsupp, -⟩ :=
    exists_disentangling_balls hd μ₀ T hT hμ hμs hne hmiss
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
  refine ⟨θ, hdur, ⟨fun i => Metric.ball (α i) r, hsupp, ?_⟩, ?_⟩
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

**Proved** by assembly on the mean-field layer (F14): disentangle the family over the first half
of the horizon (`prop_3_1`), cluster each disentangled measure to its target point in its
hemisphere over the second half (`cluster_to_point`, seven pieces each), combine the per-member
schedules into one with the parking construction (`exists_parked_schedule`), and concatenate with
the disentangler (`attnMeasureFlow_append`). Effective status `math.axiomatised`.

The sphere-supported inputs and on-sphere targets are the paper's data (D) (`μ₀^i ∈ P(S^{d-1})`,
`x^i ∈ S^{d-1}`); `Pairwise (μ₀ i ≠ μ₀ j)` is the paper's standing assumption (p. 5). The paper's
`O(d·N)` switch bound and `O(dN/T + log 1/ε)` parameter-norm bound are deferred with the
disentangling budget (non-explicit constants). -/
theorem theorem_1_1 (hd : 3 ≤ d) {N : ℕ} (μ₀ : Fin N → Measure (Eucl d)) (x : Fin N → Eucl d)
    (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε) (hmiss : SharedMissingDirection μ₀)
    (hμ : ∀ i, IsProbabilityMeasure (μ₀ i))
    (hμs : ∀ i, supportedIn (μ₀ i) (sphere d)) (hx : ∀ i, x i ∈ sphere d)
    (hne : Pairwise fun i j => μ₀ i ≠ μ₀ j) :
    ∃ θ : AttnSchedule d, AttnSchedule.durationSum θ = T ∧
      ∀ i, Axioms.W2 (attnMeasureFlow θ (μ₀ i)) (Measure.dirac (x i)) ≤ ε := by
  have hT2 : 0 < T / 2 := by linarith
  obtain ⟨θ₁, hdur₁, hdisj, hhemi⟩ := prop_3_1 hd μ₀ (T / 2) hT2 hμ hμs hne hmiss
  -- Each disentangled measure can be clustered to its prescribed target point (7 pieces).
  have hper : ∀ i, ∃ θ : AttnSchedule d, AttnSchedule.durationSum θ = T / 2 ∧
      AttnSchedule.switches θ ≤ 7 ∧
      Axioms.W2 (attnMeasureFlow θ (attnMeasureFlow θ₁ (μ₀ i))) (Measure.dirac (x i)) ≤ ε := by
    intro i
    obtain ⟨e, he, hsupp⟩ := hhemi i
    haveI := hμ i
    haveI := Foundations.isProbabilityMeasure_attnMeasureFlow θ₁ (μ₀ i) (hμs i)
    exact cluster_to_point (attnMeasureFlow θ₁ (μ₀ i)) hd (T / 2) ε hT2 hε (x i) e (hx i) he
      (Foundations.attnMeasureFlow_supportedIn_sphere θ₁ (μ₀ i) (hμs i)) hsupp
  -- Park the per-member schedules into a single schedule acting on the disjoint family.
  obtain ⟨Θ, hdurΘ, _hΘsw, hΘ⟩ :=
    exists_parked_schedule hd (fun i => attnMeasureFlow θ₁ (μ₀ i))
      (fun i => Measure.dirac (x i)) (T / 2) ε (fun _ => 7) hdisj hper
  refine ⟨θ₁ ++ Θ, ?_, fun i => ?_⟩
  · rw [AttnSchedule.durationSum_append, hdur₁, hdurΘ]; ring
  · rw [Foundations.attnMeasureFlow_append]
    exact hΘ i

/-- **Theorem 1.2** (general targets). If every input/target pair is matchable by a (measurable)
transport map and the inputs share a missing direction, then a single piecewise-constant `θ` steers
each input to within `ε` of its target in `W₂`.

**Proved** by assembly on the mean-field layer (F14): disentangle the inputs over the first half
of the horizon (`exists_disentangling_balls`, used directly for its per-member flow maps); each
disentangled measure `ν i = (μ₀ i).map Φᵢ` is then matchable to `μ₁ i` by `S = Ti ∘ Φᵢ⁻¹` (the
on-sphere inverse the axiom provides, mirroring the paper's `ψ^i = T^i ∘ (T^i_{Φ₁})⁻¹`);
approximate that transport map by a flow over the second half (`lemma_5_4`) and bound `W₂` by the
`L²` map distance (the coupling axiom L7, `W2_map_le_L2`); finally park the per-member schedules
into one (`exists_parked_schedule`) and concatenate with the disentangler. Effective status
`math.axiomatised`; the `W₂` bookkeeping is machine-checked.

The probability and sphere-support hypotheses on the inputs are the paper's data (D);
`Pairwise (μ₀ i ≠ μ₀ j)` is the paper's standing assumption. The target missing-direction
hypothesis `_hmiss₁` (the `w₁` half of eq. (1.5)) is retained for statement fidelity even though
this assembly does not consume it: the paper needs it to disentangle the TARGETS for Lemma 5.1's
gluing, a step our `exists_parked_schedule` axiom absorbs. -/
theorem theorem_1_2 (hd : 3 ≤ d) {N : ℕ} (μ₀ μ₁ : Fin N → Measure (Eucl d))
    (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (hmiss₀ : SharedMissingDirection μ₀) (_hmiss₁ : SharedMissingDirection μ₁)
    (hμ : ∀ i, IsProbabilityMeasure (μ₀ i))
    (hμ₀s : ∀ i, supportedIn (μ₀ i) (sphere d))
    (hne : Pairwise fun i j => μ₀ i ≠ μ₀ j)
    (hmatch : Matchable μ₀ μ₁) :
    ∃ θ : AttnSchedule d, AttnSchedule.durationSum θ = T ∧
      ∀ i, Axioms.W2 (attnMeasureFlow θ (μ₀ i)) (μ₁ i) ≤ ε := by
  have hT2 : 0 < T / 2 := by linarith
  obtain ⟨θ₁, α, r, hdur₁, hr0, hr1, hα, hsep, hsupp, hmaps⟩ :=
    exists_disentangling_balls hd μ₀ (T / 2) hT2 hμ hμ₀s hne hmiss₀
  -- The disentangled family has pairwise disjoint (ball) carriers.
  have hdisj : DisjointSupports (fun i => attnMeasureFlow θ₁ (μ₀ i)) :=
    ⟨fun i => Metric.ball (α i) r, hsupp, fun i j hij =>
      Metric.ball_disjoint_ball (by linarith [hsep i j hij])⟩
  have hper : ∀ i, ∃ θ : AttnSchedule d, AttnSchedule.durationSum θ = T / 2 ∧
      Axioms.W2 (attnMeasureFlow θ (attnMeasureFlow θ₁ (μ₀ i))) (μ₁ i) ≤ ε := by
    intro i
    obtain ⟨Ti, hTim, hTis, hTi⟩ := hmatch i
    obtain ⟨Φ, Φinv, hΦm, hΦinvm, hΦmap, hΦleft⟩ := hmaps i
    haveI := hμ i
    haveI : IsProbabilityMeasure (attnMeasureFlow θ₁ (μ₀ i)) :=
      Foundations.isProbabilityMeasure_attnMeasureFlow θ₁ (μ₀ i) (hμ₀s i)
    set ν : Measure (Eucl d) := attnMeasureFlow θ₁ (μ₀ i) with hν
    have hνs : supportedIn ν (sphere d) :=
      Foundations.attnMeasureFlow_supportedIn_sphere θ₁ (μ₀ i) (hμ₀s i)
    -- The input sits a.e. on the sphere, where `Φinv` inverts `Φ`.
    have hμae : ∀ᵐ w ∂(μ₀ i), w ∈ sphere d := by
      rw [ae_iff]; exact hμ₀s i
    -- ν is matchable to μ₁ i via S = Ti ∘ Φᵢ⁻¹.
    set S : Eucl d → Eucl d := Ti ∘ Φinv with hS
    have hSmeas : Measurable S := hTim.comp hΦinvm
    have hcongr : (S ∘ Φ) =ᵐ[μ₀ i] Ti := by
      filter_upwards [hμae] with w hw
      simp [hS, Function.comp_apply, hΦleft w hw]
    have hmap : ν.map S = μ₁ i := by
      rw [hΦmap, Measure.map_map hSmeas hΦm, Measure.map_congr hcongr]
      exact hTi
    -- S is a.e. sphere-valued on ν: pull back through the pushforward and cancel `Φinv ∘ Φ`.
    have hSs : ∀ᵐ y ∂ν, S y ∈ sphere d := by
      have hmeasset : MeasurableSet {y : Eucl d | S y ∈ sphere d} :=
        hSmeas Metric.isClosed_sphere.measurableSet
      rw [hΦmap, MeasureTheory.ae_map_iff hΦm.aemeasurable hmeasset]
      filter_upwards [hTis, hμae] with w hw hws
      simpa [hS, Function.comp_apply, hΦleft w hws] using hw
    obtain ⟨θ₂, ψε, hdur₂, hflow, hψεmeas, hint, hL2⟩ :=
      lemma_5_4 ν S (T / 2) ε hT2 hε hνs hSmeas hSs
    have hfe : (fun x => ‖S x - ψε x‖ ^ 2) = (fun x => ‖ψε x - S x‖ ^ 2) := by
      funext x; rw [norm_sub_rev]
    have hint' : Integrable (fun x => ‖ψε x - S x‖ ^ 2) ν := hfe ▸ hint
    refine ⟨θ₂, hdur₂, ?_⟩
    rw [hflow, ← hmap]
    calc Axioms.W2 (ν.map ψε) (ν.map S)
        ≤ Real.sqrt (∫ x, ‖ψε x - S x‖ ^ 2 ∂ν) := W2_map_le_L2 ν ψε S hψεmeas hSmeas hint'
      _ = Real.sqrt (∫ x, ‖S x - ψε x‖ ^ 2 ∂ν) := by simp_rw [norm_sub_rev]
      _ ≤ ε := hL2
  -- Extract the per-member schedules to obtain explicit switch budgets for the parking axiom
  -- (Lemma 5.4 states no bound, so each member's budget is its own schedule's count).
  choose θs hθs using hper
  obtain ⟨Θ, hdurΘ, _hΘsw, hΘ⟩ :=
    exists_parked_schedule hd (fun i => attnMeasureFlow θ₁ (μ₀ i)) μ₁ (T / 2) ε
      (fun i => AttnSchedule.switches (θs i)) hdisj
      (fun i => ⟨θs i, (hθs i).1, le_rfl, (hθs i).2⟩)
  refine ⟨θ₁ ++ Θ, ?_, fun i => ?_⟩
  · rw [AttnSchedule.durationSum_append, hdur₁, hdurΘ]; ring
  · rw [Foundations.attnMeasureFlow_append]
    exact hΘ i

end MeasureToMeasure.Statements
