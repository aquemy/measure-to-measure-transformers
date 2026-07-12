import MeasureToMeasure.Foundations.GeodesicConvex

/-!
# Voronoi cells of a target family (`prop_2_2` Stage 1)

The first piece of the resolved Stage 1 design (hybrid Voronoi cells + one-shot deficit/surplus
transportation, routed via inter-cell chains -- see the `prop-2-2-steps-2-3-campaign` project
notes): for `M` targets `x : Fin M → Eucl d`, the (open) **Voronoi cell** of target `k` is the set
of sphere points strictly closer to `x k` than to every other target. Deliberately the OPEN/STRICT
form, not the closed one: a closed half-space at the exact bisector threshold (`c = 0`, non-strict
`≤`) is NOT geodesically convex in general (an antipodal pair `y, -y` both sitting exactly on a
single bisector both satisfy the closed inequality, but their equal-weight chord normalizes `0`,
which is not on the sphere). The strict form has no such failure: `0 < ⟪α,y⟫` and `0 < ⟪α,-y⟫ =
-⟪α,y⟩` are directly contradictory, so no antipodal pair can ever co-occur in a single strict cap,
at any threshold `c ≥ 0` including `c = 0`. This is why `geodesicConvex_inner_cap` is stated with a
strict inequality in the first place.

The price of using open cells is that they do not literally partition the sphere: points sitting
exactly on a bisector (a positive-measure set is possible for adversarial `μ`, not just a
measure-zero technicality) belong to no cell. This is not fixed here -- the *deficit/surplus
transportation* step (Stage 1's next piece) treats any such leftover mass as an ordinary source a
deficient target's chain can reach past its own cell boundary to collect, exactly like drawing from
a neighboring cell's surplus. No closed-cell convexity lemma is needed anywhere in this design.
-/

namespace MeasureToMeasure.Leaves

open Set
open scoped RealInnerProductSpace

variable {d : ℕ}

/-- The **open Voronoi cell** of target `k` among `x : Fin M → Eucl d`: sphere points strictly
closer (in ambient inner product, equivalently in geodesic distance) to `x k` than to every other
target `x k'`. -/
def voronoiCell {M : ℕ} (x : Fin M → Eucl d) (k : Fin M) : Set (Eucl d) :=
  {y : Eucl d | y ∈ sphere d ∧ ∀ k' : Fin M, k' ≠ k → (⟪x k', y⟫ : ℝ) < ⟪x k, y⟫}

theorem voronoiCell_subset_sphere {M : ℕ} (x : Fin M → Eucl d) (k : Fin M) :
    voronoiCell x k ⊆ sphere d := fun _ hy => hy.1

/-- **A Voronoi cell is geodesically convex**, provided there is at least one other target
(`1 < M`) -- with a single target the cell is (vacuously) the whole sphere, which this codebase's
`GeodesicConvex` cannot express (the whole sphere fails closure on antipodal pairs), and is not
needed: Stage 1's assembly handles `M = 1` as a trivial separate case with no partition at all. -/
theorem geodesicConvex_voronoiCell {M : ℕ} (hM : 1 < M) (x : Fin M → Eucl d) (k : Fin M) :
    GeodesicConvex (voronoiCell x k) := by
  obtain ⟨k₀, hk₀⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin M) (by rwa [Fintype.card_fin]) k
  haveI : Nonempty {k' : Fin M // k' ≠ k} := ⟨⟨k₀, hk₀⟩⟩
  have heq : voronoiCell x k =
      ⋂ k' : {k' : Fin M // k' ≠ k}, {y : Eucl d | y ∈ sphere d ∧ 0 < ⟪x k - x k'.1, y⟫} := by
    ext y
    simp only [voronoiCell, Set.mem_setOf_eq, Set.mem_iInter, Subtype.forall]
    constructor
    · rintro ⟨hys, hlt⟩ k' hk'
      exact ⟨hys, by rw [inner_sub_left]; linarith [hlt k' hk']⟩
    · intro h
      refine ⟨(h k₀ hk₀).1, fun k' hk' => ?_⟩
      have hpos := (h k' hk').2
      rw [inner_sub_left] at hpos
      linarith
  rw [heq]
  exact geodesicConvex_iInter fun k' => geodesicConvex_inner_cap (x k - x k'.1) (le_refl 0)

/-- **Voronoi cells of distinct targets are disjoint.** Immediate from antisymmetry of the strict
comparison: a point strictly closer to `x k` than `x k'` cannot also be strictly closer to `x k'`
than `x k`. -/
theorem voronoiCell_disjoint {M : ℕ} (x : Fin M → Eucl d) {k k' : Fin M} (hne : k ≠ k') :
    Disjoint (voronoiCell x k) (voronoiCell x k') := by
  rw [Set.disjoint_left]
  rintro y ⟨-, hk⟩ ⟨-, hk'⟩
  exact absurd (hk k' hne.symm) (not_lt.mpr (hk' k hne).le)

end MeasureToMeasure.Leaves
