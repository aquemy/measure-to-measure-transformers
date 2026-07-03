import MeasureToMeasure.Foundations.FlowMap

/-!
# The continuity equation and its flow map (formerly axiomatised, now discharged)

The paper's central object is the continuity equation (1.3) on the sphere and its solution map
`Φ_θ^t : 𝒫(𝕊^{d-1}) → 𝒫(𝕊^{d-1})`. Historically this file *axiomatised* the well-posedness package
(the block type, the point flow map, and its Lipschitz / bijectivity / parked laws), because Mathlib
has no theory of the continuity equation or mean-field flow maps.

The M3 foundation (`Foundations/FlowMap.lean`) now **builds** that package from Mathlib's
Picard-Lindelöf and Grönwall: a `Block` is a globally-Lipschitz, globally-bounded, radially-tangent
velocity field with a duration, and `flowMap θ t` is the fold of the per-block characteristic flows.
This file therefore no longer introduces axioms: it `export`s the concrete `Block` / `flowMap` into
the `Axioms` namespace (so every downstream `Axioms.Block` / `Axioms.flowMap` reference is an alias to
the *same* declaration -- no collision, no re-axiomatisation) and re-derives the structural interface
as ordinary theorems. The old axiom names survive as theorems with identical signatures, so no
consumer changes.
-/

namespace MeasureToMeasure.Axioms

open MeasureTheory

variable {d : ℕ}

/- Discharged: the block type is the concrete `MeasureToMeasure.Block` -- a globally-Lipschitz,
globally-bounded, radially-tangent velocity field with a nonnegative duration; `flowMap` is the fold of
the per-block characteristic flows; `Params` is the block list and `switches` its length. `export`
(rather than fresh definitions) makes `Axioms.Block` / `Axioms.flowMap` / `Axioms.Params` /
`Axioms.switches` *aliases* of the Foundations declarations, so the two layers share a single
declaration each and never collide in a consumer that has both namespaces open. A piecewise-constant
schedule `θ` is thus a finite list of blocks: composition is concatenation, the identity schedule is
the empty list, time-reversal reverses (and negates) the blocks, and the switch count is the block
count -- the schedule algebra is *proved*, not assumed. -/
export MeasureToMeasure (Block flowMap Params switches)

/-- The solution map `Φ_θ^t : 𝒫(𝕊^{d-1}) → 𝒫(𝕊^{d-1})` of the continuity equation, acting on
measures. **Defined** as the pushforward of the point flow map `flowMap θ t` -- this is precisely the
continuity equation's defining property (mass is transported along characteristics). With this,
`measureFlow_map` is definitional and the semigroup laws (`measureFlow_comp`, `_id`, `_inv`) are
*derived* from the point-level flow facts plus `Measure.map_map` / `Measure.map_id`. -/
noncomputable def measureFlow (θ : Params d) (t : ℝ) (μ : MeasureTheory.Measure (Eucl d)) :
    MeasureTheory.Measure (Eucl d) :=
  μ.map (flowMap θ t)

/-- **Mass retention under a set-mapping (the measure-theoretic half of B.8).** If the flow at time
`T ≥ 0` maps `S` into a measurable set `A`, then the transported measure of `A` is at least the
original measure of `S`: `μ S ≤ measureFlow θ T μ A`. This turns a *point-level* reaching statement
(every point of `S` flows into `A`) into a *mass* statement, via the pushforward
`measureFlow = μ.map (flowMap θ T)` and `measure_mono` on the preimage `S ⊆ (flowMap θ T)⁻¹ A`. -/
theorem le_measureFlow_of_mapsTo (θ : Params d) {T : ℝ} (hT : 0 ≤ T)
    (μ : MeasureTheory.Measure (Eucl d)) {S A : Set (Eucl d)} (hA : MeasurableSet A)
    (hmaps : Set.MapsTo (flowMap θ T) S A) :
    μ S ≤ measureFlow θ T μ A := by
  rw [measureFlow, Measure.map_apply (MeasureToMeasure.measurable_flowMap θ hT) hA]
  exact measure_mono (fun x hx => hmaps hx)

/-- The flow map is Lipschitz for **every** time `t` (well-posedness of the characteristic ODE, plus
time-reversal for `t < 0`). Discharged from `MeasureToMeasure.exists_lipschitzWith_flowMap`. -/
theorem flowMap_lipschitz (θ : Params d) (t : ℝ) :
    ∃ K : ℝ, LipschitzWith K.toNNReal (flowMap θ t) := by
  obtain ⟨K, hK⟩ := MeasureToMeasure.exists_lipschitzWith_flowMap θ t
  exact ⟨(K : ℝ), by rwa [Real.toNNReal_coe]⟩

/-- The flow map is invertible (the dynamics are time-reversible). Discharged from
`MeasureToMeasure.flowMap_bijective`. -/
theorem flowMap_bijective (θ : Params d) (t : ℝ) : Function.Bijective (flowMap θ t) :=
  MeasureToMeasure.flowMap_bijective θ t

/-- **Parked region.** A point is parked when *every* block of the schedule switches its velocity off
there (the field vanishes). Concrete realisation of the paper's `(B.2)` "act on one measure at a time"
property. -/
def Parked (θ : Params d) (S : Set (Eucl d)) : Prop := ∀ b ∈ θ, ∀ x ∈ S, b.field x = 0

/-- A parked point is left invariant by the flow: where every block's field vanishes, the integral
curve is constant, so the whole schedule fixes the point. Discharged from
`MeasureToMeasure.flowMap_fixed_of_forall_field_zero`. -/
theorem flowMap_id_on_parked (θ : Params d) (t : ℝ) {S : Set (Eucl d)} (hS : Parked θ S)
    {x : Eucl d} (hx : x ∈ S) : flowMap θ t x = x :=
  MeasureToMeasure.flowMap_fixed_of_forall_field_zero θ t (fun b hb => hS b hb x hx)

end MeasureToMeasure.Axioms
