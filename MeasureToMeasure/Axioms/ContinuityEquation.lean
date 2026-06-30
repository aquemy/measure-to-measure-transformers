import MeasureToMeasure.Foundations.Sphere

/-!
# Labeled axioms: the continuity equation and its flow map

The paper's central object is the continuity equation (1.3) on the sphere and its solution map
`Φ_θ^t : 𝒫(𝕊^{d-1}) → 𝒫(𝕊^{d-1})`. Mathlib has Picard-Lindelöf and Grönwall for ODEs, but no
theory of the continuity equation, weak measure solutions, or mean-field flow maps. We axiomatize
the well-posedness package and the structural properties (Lipschitz, invertible, time-reversible,
identity off the support) that the proofs use.
-/

namespace MeasureToMeasure.Axioms

open MeasureTheory

variable {d : ℕ}

/-- A piecewise-constant parameter schedule `θ` for the velocity field. Kept opaque here; the
analytic content lives in the axioms below. -/
axiom Params (d : ℕ) : Type

/-- AXIOM: the flow map `Φ_θ^t` on points of the sphere induced by the characteristics of the
continuity equation. Lipschitz-continuous and invertible (see the structural axioms). -/
axiom flowMap (θ : Params d) (t : ℝ) : Eucl d → Eucl d

/-- AXIOM: the solution map `Φ_θ^t : 𝒫(𝕊^{d-1}) → 𝒫(𝕊^{d-1})` of the continuity equation, acting on
measures. This is the object the main theorems control. It is the pushforward of the point flow map,
but with no Mathlib continuity-equation theory we take it as a primitive. -/
axiom measureFlow (θ : Params d) (t : ℝ) : MeasureTheory.Measure (Eucl d) →
    MeasureTheory.Measure (Eucl d)

/-- AXIOM: the number of parameter switches of a piecewise-constant schedule `θ` (the depth proxy
discussed in Section 1.4.3 and Section 6). -/
axiom switches (θ : Params d) : ℕ

/-- AXIOM: the flow map is Lipschitz on `[0, T]` (well-posedness of the characteristic ODE). -/
axiom flowMap_lipschitz (θ : Params d) (t : ℝ) : ∃ K : ℝ, LipschitzWith K.toNNReal (flowMap θ t)

/-- AXIOM: the flow map is invertible (the dynamics are time-reversible). -/
axiom flowMap_bijective (θ : Params d) (t : ℝ) : Function.Bijective (flowMap θ t)

/-- AXIOM: a point in a region `S` on which the chosen parameters switch off the velocity is left
invariant by the flow (the `(B.2)` "act on one measure at a time" property). The predicate `Parked`
abstracts "the gate is identically zero on `S`". -/
axiom Parked (θ : Params d) (S : Set (Eucl d)) : Prop

axiom flowMap_id_on_parked (θ : Params d) (t : ℝ) {S : Set (Eucl d)} (hS : Parked θ S)
    {x : Eucl d} (hx : x ∈ S) : flowMap θ t x = x

end MeasureToMeasure.Axioms
