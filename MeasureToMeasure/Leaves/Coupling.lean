import MeasureToMeasure.Axioms.Wasserstein

/-!
# Leaf L7: the linearized optimal-transport bound (Lemma 5.2)

Lemma 5.2 states `W₂(T¹_# μ, T²_# μ) ≲ ‖T¹ - T²‖_{L²(μ)}`, via the coupling `(T¹, T²)_# μ`. This is a
pure optimal-transport fact, now **machine-checked**: `W2_map_le_L2` is a proved theorem over the
`ℝ≥0∞` Kantorovich cost (`Foundations/Wasserstein.lean`), so this leaf is too. The measurability and
integrability hypotheses are what make the `ℝ≥0∞ → ℝ` bridge sound (they hold for the bounded maps on
the sphere the paper uses).
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory MeasureToMeasure.Axioms

variable {d : ℕ}

/-- L7 (Lemma 5.2): the `W₂` distance between two pushforwards of `μ` is bounded by the `L²(μ)`
distance of the maps. Machine-checked via `W2_map_le_L2`. -/
theorem lemma_5_2 (μ : Measure (Eucl d)) (T₁ T₂ : Eucl d → Eucl d)
    (hT₁ : Measurable T₁) (hT₂ : Measurable T₂)
    (hint : Integrable (fun x => ‖T₁ x - T₂ x‖ ^ 2) μ) :
    Axioms.W2 (μ.map T₁) (μ.map T₂) ≤ Real.sqrt (∫ x, ‖T₁ x - T₂ x‖ ^ 2 ∂μ) :=
  W2_map_le_L2 μ T₁ T₂ hT₁ hT₂ hint

end MeasureToMeasure.Leaves
