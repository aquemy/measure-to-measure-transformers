import MeasureToMeasure.Axioms.ContinuityEquation

/-!
# Labeled axioms: the structural algebra of the flow

`ContinuityEquation.lean` introduces the flow map `Φ_θ^t` (`flowMap`), its measure action
(`measureFlow`), the switch count, and the parking property. To *assemble* the paper's construction
`Φ_fin = (Φ_θ₁)⁻¹ ∘ Φ_θ₂ ∘ Φ_θ₁` out of the mid-level lemmas, we additionally need the algebraic
structure of piecewise-constant schedules: sequential composition, its effect on the switch count,
time-reversal, and the pushforward identity linking the point flow to the measure flow.

Mathlib has no continuity-equation theory, so these are taken as **labeled axioms** (status
`math.axiomatised`); each encodes a standard well-posedness / semigroup fact. They are *structural*
(they describe how schedules combine), never a mathematical conclusion of the paper: the headline
theorems are still *proved* by assembling the mid-level results over this algebra, so the kernel
verifies the paper's logical skeleton modulo this documented surface.
-/

namespace MeasureToMeasure.Axioms

open MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- The flow map is measurable: it is Lipschitz (`flowMap_lipschitz`), hence continuous, hence Borel
measurable. Used throughout to evaluate the pushforward `measureFlow`. -/
theorem flowMap_measurable (θ : Params d) (t : ℝ) : Measurable (flowMap θ t) := by
  obtain ⟨K, hK⟩ := flowMap_lipschitz θ t
  exact hK.continuous.measurable

/-- AXIOM (identity schedule). The empty parameter programme: it runs no velocity field, so its flow
is the identity and it costs no switches. The unit for `comp`. -/
axiom idParams (d : ℕ) : Params d

/-- AXIOM (point level): the identity schedule's flow map is the identity (it runs no velocity). More
primitive than the former measure-level `measureFlow_id`, which is now derived. -/
axiom flowMap_id (t : ℝ) : flowMap (idParams d) t = id

/-- The identity schedule leaves every measure unchanged. Derived from `flowMap_id` and
`Measure.map_id` now that `measureFlow` is the pushforward of `flowMap`. -/
theorem measureFlow_id (t : ℝ) (μ : Measure (Eucl d)) : measureFlow (idParams d) t μ = μ := by
  show μ.map (flowMap (idParams d) t) = μ
  rw [flowMap_id, Measure.map_id]

/-- AXIOM: the identity schedule has zero switches. -/
axiom switches_id : switches (idParams d) = 0

/-- AXIOM (sequential composition of schedules). `comp θ₁ θ₂` is the piecewise-constant schedule that
runs `θ₁` first and then `θ₂` (concatenation of the two parameter programmes over `[0, T]`). Encodes
the time-additivity of the continuity-equation flow / the depth-stacking of two Transformer blocks. -/
axiom comp (θ₁ θ₂ : Params d) : Params d

/-- AXIOM (composition on points). The composite schedule's flow map is the composition of the two
flow maps: the characteristics of `θ₁` followed by those of `θ₂`. -/
axiom flowMap_comp (θ₁ θ₂ : Params d) (T : ℝ) :
    flowMap (comp θ₁ θ₂) T = flowMap θ₂ T ∘ flowMap θ₁ T

/-- The composite schedule's solution map is the composition of the two solution maps (the measure-level
shadow of `flowMap_comp`). Derived from `flowMap_comp` and `Measure.map_map`. -/
theorem measureFlow_comp (θ₁ θ₂ : Params d) (T : ℝ) (μ : Measure (Eucl d)) :
    measureFlow (comp θ₁ θ₂) T μ = measureFlow θ₂ T (measureFlow θ₁ T μ) := by
  show μ.map (flowMap (comp θ₁ θ₂) T) = (μ.map (flowMap θ₁ T)).map (flowMap θ₂ T)
  rw [flowMap_comp, Measure.map_map (flowMap_measurable θ₂ T) (flowMap_measurable θ₁ T)]

/-- AXIOM (switch sub-additivity). Concatenating two schedules costs at most the sum of their
switches (one extra boundary is absorbed into the count). This drives every switch-budget bound. -/
axiom switches_comp (θ₁ θ₂ : Params d) :
    switches (comp θ₁ θ₂) ≤ switches θ₁ + switches θ₂

/-- AXIOM (time-reversal). `inv θ` is the schedule whose flow undoes that of `θ` (the dynamics are
time-reversible, `flowMap_bijective`). This realizes the un-disentangling factor `(Φ_θ₁)⁻¹`. -/
axiom inv (θ : Params d) : Params d

/-- AXIOM (point level): the reverse schedule's flow map is a left inverse of the forward one. More
primitive than the former measure-level `measureFlow_inv`, which is now derived; consistent with
`flowMap_bijective`. -/
axiom flowMap_inv (θ : Params d) (T : ℝ) : flowMap (inv θ) T ∘ flowMap θ T = id

/-- The reverse schedule cancels the forward one at the measure level. Derived from `flowMap_inv`,
`Measure.map_map`, and `Measure.map_id`. -/
theorem measureFlow_inv (θ : Params d) (T : ℝ) (μ : Measure (Eucl d)) :
    measureFlow (inv θ) T (measureFlow θ T μ) = μ := by
  show (μ.map (flowMap θ T)).map (flowMap (inv θ) T) = μ
  rw [Measure.map_map (flowMap_measurable (inv θ) T) (flowMap_measurable θ T), flowMap_inv,
    Measure.map_id]

/-- Pushforward identity: the solution map is the pushforward of the point flow map,
`Φ_θ^t(μ) = (Φ_θ^t)_# μ`. Now **definitional** (`measureFlow` is defined as the pushforward), so this
is `rfl`; kept as a named lemma because it is the bridge that turns a point-level steering statement
`flowMap θ T (x i) = y i` into a measure-level `measureFlow θ T (δ_{x i}) = δ_{y i}`. -/
theorem measureFlow_map (θ : Params d) (t : ℝ) (μ : Measure (Eucl d)) :
    measureFlow θ t μ = μ.map (flowMap θ t) := rfl

/-- The solution map sends a Dirac mass to the Dirac mass at the image point: a direct consequence of
the pushforward identity (`measureFlow_map`) and `Measure.map_dirac` (needs measurability). -/
theorem measureFlow_dirac (θ : Params d) (t : ℝ) (z : Eucl d) :
    measureFlow θ t (Measure.dirac z) = Measure.dirac (flowMap θ t z) := by
  simp [measureFlow_map, flowMap_measurable θ t]

/-- The solution map preserves probability measures: it is the pushforward under a measurable map. -/
theorem isProbabilityMeasure_measureFlow (θ : Params d) (t : ℝ) (μ : Measure (Eucl d))
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (measureFlow θ t μ) := by
  rw [measureFlow_map]
  exact ⟨by
    rw [Measure.map_apply (flowMap_measurable θ t) MeasurableSet.univ, Set.preimage_univ]
    exact measure_univ⟩

/-- The pushforward of a finite weighted sum of measures is the weighted sum of the pushforwards. -/
theorem map_finsetSum_smul {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ≥0∞)
    (P : ι → Measure (Eucl d)) {f : Eucl d → Eucl d} (hf : Measurable f) :
    (∑ i ∈ s, a i • P i).map f = ∑ i ∈ s, a i • (P i).map f := by
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, Measure.map_add _ _ hf, Measure.map_smul, ih]

/-- The solution map distributes over a finite weighted sum of measures (it is a pushforward). -/
theorem measureFlow_sum_smul {M : ℕ} (θ : Params d) (t : ℝ) (a : Fin M → ℝ≥0∞)
    (P : Fin M → Measure (Eucl d)) :
    measureFlow θ t (∑ k, a k • P k) = ∑ k, a k • measureFlow θ t (P k) := by
  simp only [measureFlow_map]
  exact map_finsetSum_smul Finset.univ a P (flowMap_measurable θ t)

end MeasureToMeasure.Axioms
