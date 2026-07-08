import MeasureToMeasure.Foundations.TrajectoryFieldPicardLindelof

/-!
# Sphere invariance of the trajectory-composed integral curve (M3b existence, leaf E3f)

The outer self-consistency map evaluates the frozen-field flow along a trial trajectory `η`, and
needs the resulting point trajectories to stay on the sphere (so their pushforward measures are
again sphere-supported, landing back in `SphereProb d`). This leaf supplies that fact directly from
the radial-tangency machinery already banked for a single frozen measure (`attnFieldExt_radial`,
`abs_two_attnGate_le`, both already uniform over ANY sphere-supported probability measure, no new
estimate needed) and the general Grönwall core (`SphereFlow.norm_sq_eq_one_of_radial_tangent`):

any integral curve of the trajectory-composed field `ẋ = trajectoryField p hT η t x` that starts on
the sphere stays on the sphere throughout `[0,T]`, exactly as `Block.blockFlow_mem_sphere` shows for
a single frozen block, but now with the gate/drift evaluated along the moving measure `η t` instead
of a fixed `ν`.

M3b staging: consumed when `exists_meanFieldFlow` is discharged; see RESEARCH.md.
-/

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace MeasureToMeasure.Foundations

variable {d : ℕ}

/-- **Sphere invariance for the trajectory-composed characteristic ODE.** Any integral curve `x` of
`ẋ = trajectoryField p hT η t x` on `[0,T]` that starts on the sphere stays on the sphere throughout
-- the radial-tangency identity and gate bound hold uniformly over every sphere-supported
probability measure `η t`, so the Grönwall sphere-invariance argument applies exactly as for a
single frozen measure. -/
theorem trajectoryField_mem_sphere (p : AttnParams d) {T : ℝ} (hT : 0 ≤ T)
    (η : C(Set.Icc (0 : ℝ) T, SphereProb d))
    {x : ℝ → Eucl d} (hx' : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt x (trajectoryField p hT η t (x t)) t)
    (hx0 : x 0 ∈ sphere d) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, x t ∈ sphere d := by
  have hnorm := norm_sq_eq_one_of_radial_tangent
    (x := x) (v := fun t => trajectoryField p hT η t (x t))
    (c := fun t => attnGate p (η (Set.projIcc 0 T hT t)).val (x t))
    (K := 4 * fieldBallBound p) (T := T)
    hx'
    (fun t _ => attnFieldExt_radial p (η (Set.projIcc 0 T hT t)).val (x t))
    (fun t _ => by
      haveI := (η (Set.projIcc 0 T hT t)).property.1
      exact abs_two_attnGate_le p (η (Set.projIcc 0 T hT t)).val
        (η (Set.projIcc 0 T hT t)).property.2 (x t))
    (norm_eq_one_of_mem_sphere hx0)
  intro t ht
  have h1 := hnorm t ht
  simpa [sphere, Metric.mem_sphere, dist_eq_norm] using h1

end MeasureToMeasure.Foundations
