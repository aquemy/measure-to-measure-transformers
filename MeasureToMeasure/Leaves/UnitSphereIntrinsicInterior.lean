import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.InnerProductSpace.Convex

/-!
# A unit-norm point in the intrinsic interior of a ball-confined hull forces a singleton hull

Support lemma for the `lemma_3_4_part2` non-vacuous re-discharge campaign (G1, finding F25's
kernel gate): if `S` sits inside the closed unit ball and some UNIT-norm `u` lies in the
`intrinsicInterior` of `convexHull ℝ S`, then the hull is the singleton `{u}`.

The geometry: were the hull to contain any `y ≠ u`, intrinsic-interior membership would let the
segment from `y` through `u` be prolonged PAST `u` by a small `t > 0` while staying in the hull
(the prolonged point stays in the affine span, and the interior-of-preimage membership defining
`intrinsicInterior` is open along the continuous line path). That places `u` strictly BETWEEN two
distinct hull points, and the closed unit ball of an inner-product space is strictly convex
(`strictConvex_closedBall`), so `u` would fall in the OPEN unit ball, contradicting `‖u‖ = 1`.
So a unit-norm intrinsic-interior point is only possible for a degenerate, single-point hull.

Deliberately stated over an ABSTRACT real inner-product space, in a file importing NO
project-specific `Eucl d`-touching content: `Eucl d = EuclideanSpace ℝ (Fin d)`'s instances (via
`PiLp`) are definitionally heavy enough that elaborating subtype-topology unification INSIDE a
proof like this can time out when they are in scope (see `Leaves/UniformRadiusPacking.lean` for
the precedent). Callers needing the `Eucl d` case should APPLY this already-proven theorem, not
re-elaborate its tactic proof with `Eucl d` in scope. Consumed by
`Regression/Refuted/HuUnitBarycenterStrictConvexity.lean` (the F25 refutation record).
-/

set_option autoImplicit false

namespace MeasureToMeasure.Leaves

open Metric

/-- **A unit-norm intrinsic-interior point collapses a ball-confined hull to a point.** If
`S ⊆ closedBall 0 1` and a unit-norm `u` lies in `intrinsicInterior ℝ (convexHull ℝ S)`, then
`convexHull ℝ S = {u}`: any second hull point `y ≠ u` would let the segment `[y, u]` be prolonged
past `u` inside the hull (openness of the intrinsic interior along the line through `y` and `u`),
putting `u` strictly between two hull points; strict convexity of the closed unit ball then forces
`‖u‖ < 1`, a contradiction. -/
theorem convexHull_eq_singleton_of_unitNorm_mem_intrinsicInterior
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {S : Set E}
    (hS : S ⊆ Metric.closedBall 0 1) {u : E} (hu1 : ‖u‖ = 1)
    (hu : u ∈ intrinsicInterior ℝ (convexHull ℝ S)) :
    convexHull ℝ S = {u} := by
  have huC : u ∈ convexHull ℝ S := intrinsicInterior_subset hu
  have hCball : convexHull ℝ S ⊆ Metric.closedBall 0 1 :=
    convexHull_min hS (convex_closedBall 0 1)
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨huC, fun y hyC => ?_⟩
  by_contra hyu
  obtain ⟨û, hûint, hûval⟩ := mem_intrinsicInterior.mp hu
  have hu' : u ∈ affineSpan ℝ (convexHull ℝ S) := subset_affineSpan _ _ huC
  have hy' : y ∈ affineSpan ℝ (convexHull ℝ S) := subset_affineSpan _ _ hyC
  -- the whole line through `y` and `u`, parametrized as `t ↦ u + t • (u - y)`, stays in the span
  have hmem : ∀ t : ℝ, u + t • (u - y) ∈ affineSpan ℝ (convexHull ℝ S) := by
    intro t
    have h := AffineSubspace.smul_vsub_vadd_mem (affineSpan ℝ (convexHull ℝ S)) t hu' hy' hu'
    rw [vsub_eq_sub, vadd_eq_add, add_comm] at h
    exact h
  set ψ : ℝ → affineSpan ℝ (convexHull ℝ S) := fun t => ⟨u + t • (u - y), hmem t⟩ with hψ
  have hψcont : Continuous ψ := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hψ0 : ψ 0 = û := by
    apply Subtype.ext
    rw [hûval]
    simp [hψ]
  -- openness of the interior-of-preimage along `ψ` yields a small `t > 0` still inside the hull
  have hopen : IsOpen (ψ ⁻¹' interior ((Subtype.val :
      affineSpan ℝ (convexHull ℝ S) → E) ⁻¹' (convexHull ℝ S))) :=
    isOpen_interior.preimage hψcont
  have h0mem : (0 : ℝ) ∈ ψ ⁻¹' interior ((Subtype.val :
      affineSpan ℝ (convexHull ℝ S) → E) ⁻¹' (convexHull ℝ S)) := by
    rw [Set.mem_preimage, hψ0]; exact hûint
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 h0mem
  have htpos : 0 < ε / 2 := by positivity
  have h1t : (0 : ℝ) < 1 + ε / 2 := by linarith
  have htmem : ψ (ε / 2) ∈ interior ((Subtype.val :
      affineSpan ℝ (convexHull ℝ S) → E) ⁻¹' (convexHull ℝ S)) := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos htpos]
    linarith
  have hz' : ψ (ε / 2) ∈ (Subtype.val :
      affineSpan ℝ (convexHull ℝ S) → E) ⁻¹' (convexHull ℝ S) := interior_subset htmem
  have hz : u + (ε / 2) • (u - y) ∈ convexHull ℝ S := hz'
  -- `u` sits strictly between `y` and the prolonged point `z := u + (ε/2) • (u - y)`
  have hyz : y ≠ u + (ε / 2) • (u - y) := by
    intro h
    apply hyu
    have h1 : (1 + ε / 2) • (y - u) = 0 := by
      have h2 : y - (u + (ε / 2) • (u - y)) = 0 := sub_eq_zero.mpr h
      calc (1 + ε / 2) • (y - u) = y - (u + (ε / 2) • (u - y)) := by module
        _ = 0 := h2
    rcases smul_eq_zero.mp h1 with h3 | h3
    · exact absurd h3 (ne_of_gt h1t)
    · exact sub_eq_zero.mp h3
  have hseg : u ∈ openSegment ℝ y (u + (ε / 2) • (u - y)) := by
    refine ⟨(ε / 2) / (1 + ε / 2), 1 / (1 + ε / 2), div_pos htpos h1t,
      div_pos one_pos h1t, ?_, ?_⟩
    · field_simp
      ring
    · match_scalars <;> (field_simp; try ring)
  -- strict convexity of the closed unit ball pushes `u` into the open ball: contradiction
  have hstrict : StrictConvex ℝ (Metric.closedBall (0 : E) 1) :=
    strictConvex_closedBall ℝ (0 : E) 1
  have hint : u ∈ interior (Metric.closedBall (0 : E) 1) :=
    hstrict.openSegment_subset (hCball hyC) (hCball hz) hyz hseg
  rw [interior_closedBall (0 : E) one_ne_zero, mem_ball_zero_iff, hu1] at hint
  exact lt_irrefl 1 hint

end MeasureToMeasure.Leaves
