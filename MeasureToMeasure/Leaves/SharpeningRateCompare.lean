import MeasureToMeasure.Foundations.Projector
import MeasureToMeasure.Leaves.BarycenterNonColinear

/-!
# Colinear barycenters give an exact `pAlign`-field relation (`phase4_pole_specific_pair`, group A)

`tangentialProjector` is exactly linear in its vector argument (`tangentialProjector_smul`,
`Foundations/Projector.lean`). Combined with the colinearity hypothesis that motivates the
Appendix B.3 asymmetric-cap route (`barycenter μ0 = γ1 • barycenter ν0`, replacing the now-known-false
`hgenRest` route), this gives an EXACT pointwise relation between the two measures' `pAlign` fields
(`Leaves/TaylorRemainderBound.lean`'s `pAlign_field`) at any shared point `x`, with no error term: the
field driving `μ0`'s flow at `x` is exactly `γ1` times the field driving `ν0`'s flow at `x`. This is
the foundation the single-pole-pigeonhole route builds on.
-/

namespace MeasureToMeasure.Leaves

variable {d : ℕ}

/-- Colinear barycenters give an exact `tangentialProjector`-scaled relation, via
`tangentialProjector`'s exact linearity in its vector argument. -/
theorem colinear_tangentialProjector_eq {μ0 ν0 : MeasureTheory.Measure (Eucl d)} {γ1 : ℝ}
    (hcol : barycenter μ0 = γ1 • barycenter ν0) (x : Eucl d) :
    tangentialProjector x (barycenter μ0) = γ1 • tangentialProjector x (barycenter ν0) := by
  rw [hcol, tangentialProjector_smul]

end MeasureToMeasure.Leaves
