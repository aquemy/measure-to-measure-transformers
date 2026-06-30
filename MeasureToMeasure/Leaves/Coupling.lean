import MeasureToMeasure.Axioms.Wasserstein

/-!
# Leaf L7: the linearized optimal-transport bound (Lemma 5.2)

Lemma 5.2 states `W₂(T¹_# μ, T²_# μ) ≲ ‖T¹ - T²‖_{L²(μ)}`, via the coupling `(T¹, T²)_# μ`. This is a
pure optimal-transport fact. Mathlib `v4.31.0` has no `W₂`, so it rests on the labeled axiom
`W2_map_le_L2`. Accordingly this result is `math.axiomatised`, not `math.machine-checked`: its CKC
effective status is the minimum over its dependency closure, which contains the `W2` axiom.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory MeasureToMeasure.Axioms

variable {d : ℕ}

/-- L7 (Lemma 5.2): the `W₂` distance between two pushforwards of `μ` is bounded by the `L²(μ)`
distance of the maps. Rests on the optimal-transport axiom `W2_map_le_L2`. -/
theorem lemma_5_2 (μ : Measure (Eucl d)) (T₁ T₂ : Eucl d → Eucl d) :
    W2 (μ.map T₁) (μ.map T₂) ≤ Real.sqrt (∫ x, ‖T₁ x - T₂ x‖ ^ 2 ∂μ) :=
  W2_map_le_L2 μ T₁ T₂

end MeasureToMeasure.Leaves
