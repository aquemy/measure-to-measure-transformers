import MeasureToMeasure.Axioms.Dynamics
import MeasureToMeasure.Leaves.BarycenterNonColinear

/-!
# Leaf L1 (Lemma 3.4): the barycenter of a flowed measure is the flow-averaged input

The barycenter clause of Lemma 3.4 (Parts 1 and 2) and Lemma 3.3 all read the barycenter of a
*flowed* measure, `ℰ_{Φ_θ^t μ}`. Because the solution map is the pushforward of the point flow map
(`measureFlow_map`, definitional), this is exactly the `μ`-average of the flowed points:

  `barycenter (measureFlow θ t μ) = ∫ x, flowMap θ t x ∂μ`.

This is the bridge that turns the measure-level barycenter obligation into a point-level integral
against `μ`, where the perceptron construction (a `Block`'s field) actually acts. It is the
`integral_map` change of variables for `id`, valid for `t ≥ 0` (where `flowMap θ t` is measurable);
no integrability hypothesis is needed — `integral_map` transports the integral unconditionally.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory
open MeasureToMeasure.Axioms (measureFlow measureFlow_map)

variable {d : ℕ}

/-- **L1.** The barycenter of a flowed measure equals the `μ`-average of the flowed points:
`ℰ_{Φ_θ^t μ} = ∫ Φ_θ^t(x) dμ(x)`. The solution map is the pushforward (`measureFlow_map`), so this
is the `integral_map` change of variables for the identity integrand; it needs only measurability of
`flowMap θ t` (hence `t ≥ 0`), not integrability. -/
theorem barycenter_measureFlow (θ : Params d) {t : ℝ} (ht : 0 ≤ t) (μ : Measure (Eucl d)) :
    barycenter (measureFlow θ t μ) = ∫ x, flowMap θ t x ∂μ := by
  rw [barycenter, measureFlow_map]
  exact integral_map (measurable_flowMap θ ht).aemeasurable aestronglyMeasurable_id

end MeasureToMeasure.Leaves
