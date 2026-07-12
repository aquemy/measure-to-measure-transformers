import MeasureToMeasure.Foundations.GeodesicConvex
import MeasureToMeasure.Foundations.SphereMeasureBridge

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
measure-zero technicality) belong to no cell. Unlike an earlier draft of this design, this leftover
mass canNOT simply be bolted on as an extra source fed into an otherwise cell-only supply/demand
routing: if `Leftover := 1 - Σₖ μ(voronoiCell x k) > 0`, total deficit exceeds total surplus by
EXACTLY `Leftover` (`Σ(αₖ-βₖ)⁺ - Σ(βₖ-αₖ)⁺ = Σ(αₖ-βₖ) = 1-Σβₖ = Leftover`, since `Σαₖ=1`), so a
surplus-only routing graph is under-supplied by construction whenever boundary mass is positive.
The fix is `voronoiCell'` below: a CLOSED, lexicographically tie-broken cell family that DOES
partition the sphere exactly (`Σₖ μ(voronoiCell' x k) = 1`), giving a genuinely balanced
transportation problem with no pseudo-source needed. `voronoiCell'` is not claimed to be
geodesically convex (it generally is not, for the same reason a bare closed half-space at `c=0`
fails); it is used only for the mass-accounting split. The actual geometric realization keeps using
the proven-convex OPEN `voronoiCell x k` for each target's core arm, treating the small residual
slice `voronoiCell' x k \ voronoiCell x k` as one more (thin, but positive-measure-capable) donor
region reached by its own short chain -- structurally identical to reaching into a genuine
surplus neighbor, not a special case.
-/

namespace MeasureToMeasure.Leaves

open Set MeasureTheory
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

/-- The **tie-broken closed Voronoi cell**: `k` such that `x k` maximizes `⟪·,y⟫` over all targets,
with ties broken toward the SMALLEST index. Used only for exact mass accounting
(`voronoiCell'_disjoint` + `voronoiCell'_covers` give a genuine partition of the sphere); NOT claimed
geodesically convex. -/
def voronoiCell' {M : ℕ} (x : Fin M → Eucl d) (k : Fin M) : Set (Eucl d) :=
  {y : Eucl d | y ∈ sphere d ∧ (∀ k' : Fin M, (⟪x k', y⟫ : ℝ) ≤ ⟪x k, y⟫) ∧
    ∀ k' : Fin M, k' < k → (⟪x k', y⟫ : ℝ) < ⟪x k, y⟫}

theorem voronoiCell_subset_voronoiCell' {M : ℕ} (x : Fin M → Eucl d) (k : Fin M) :
    voronoiCell x k ⊆ voronoiCell' x k := by
  rintro y ⟨hys, hlt⟩
  exact ⟨hys, fun k' => (eq_or_ne k' k).elim (fun h => h ▸ le_refl _) (fun h => (hlt k' h).le),
    fun k' hk' => hlt k' hk'.ne⟩

/-- **Tie-broken cells of distinct targets are disjoint.** If `k < k'` both claimed `y`, `k'`'s own
tie-break (strict win against every smaller index, in particular `k`) contradicts `k`'s own global
maximality (weakly beating `k'`). -/
theorem voronoiCell'_disjoint {M : ℕ} (x : Fin M → Eucl d) {k k' : Fin M} (hne : k ≠ k') :
    Disjoint (voronoiCell' x k) (voronoiCell' x k') := by
  rw [Set.disjoint_left]
  rintro y ⟨-, hmaxk, hstrictk⟩ ⟨-, hmaxk', hstrictk'⟩
  rcases Fin.lt_or_lt_of_ne hne with hlt | hlt
  · exact absurd (hstrictk' k hlt) (not_lt.mpr (hmaxk k'))
  · exact absurd (hstrictk k' hlt) (not_lt.mpr (hmaxk' k))

/-- **The tie-broken cells cover the sphere.** `Fin M` is finite, so `k ↦ ⟪x k, y⟫` attains a
maximum; among all maximizers (a nonempty finite set), the smallest index is exactly the `k` with
`y ∈ voronoiCell' x k`. -/
theorem voronoiCell'_covers {M : ℕ} (hM : 0 < M) (x : Fin M → Eucl d) {y : Eucl d}
    (hy : y ∈ sphere d) : ∃ k : Fin M, y ∈ voronoiCell' x k := by
  set S : Finset (Fin M) := Finset.univ.filter (fun k => ∀ k' : Fin M, (⟪x k', y⟫ : ℝ) ≤ ⟪x k, y⟫)
    with hSdef
  have hSne : S.Nonempty := by
    obtain ⟨k, -, hk⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin M))
      (fun k => (⟪x k, y⟫ : ℝ)) ⟨⟨0, hM⟩, Finset.mem_univ _⟩
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, fun k' => hk k' (Finset.mem_univ k')⟩⟩
  refine ⟨S.min' hSne, hy, (Finset.mem_filter.mp (S.min'_mem hSne)).2, fun k' hk' => ?_⟩
  by_contra hcon
  push Not at hcon
  have hmaxk0 := (Finset.mem_filter.mp (S.min'_mem hSne)).2
  have heq : (⟪x (S.min' hSne), y⟫ : ℝ) = ⟪x k', y⟫ := le_antisymm hcon (hmaxk0 k')
  have hk'mem : k' ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ k',
    fun k'' => heq ▸ (hmaxk0 k'' : (⟪x k'', y⟫ : ℝ) ≤ ⟪x (S.min' hSne), y⟫)⟩
  exact absurd (S.min'_le k' hk'mem) (not_le.mpr hk')

/-- The tie-broken cells are measurable: a finite conjunction of `≤`/`<` comparisons between
continuous linear functionals of `y`, intersected with the (measurable) sphere. -/
theorem measurableSet_voronoiCell' {M : ℕ} (x : Fin M → Eucl d) (k : Fin M) :
    MeasurableSet (voronoiCell' x k) := by
  refine (measurableSet_sphere d).inter (MeasurableSet.inter ?_ ?_)
  · show MeasurableSet {y : Eucl d | ∀ k' : Fin M, (⟪x k', y⟫ : ℝ) ≤ ⟪x k, y⟫}
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun k' => measurableSet_le
      (f := fun y : Eucl d => (⟪x k', y⟫ : ℝ)) (g := fun y : Eucl d => (⟪x k, y⟫ : ℝ))
      (by fun_prop) (by fun_prop)
  · show MeasurableSet {y : Eucl d | ∀ k' : Fin M, k' < k → (⟪x k', y⟫ : ℝ) < ⟪x k, y⟫}
    rw [Set.setOf_forall]
    refine MeasurableSet.iInter fun k' => ?_
    by_cases hlt : k' < k
    · show MeasurableSet {y : Eucl d | k' < k → (⟪x k', y⟫ : ℝ) < ⟪x k, y⟫}
      have heq2 : {y : Eucl d | k' < k → (⟪x k', y⟫ : ℝ) < ⟪x k, y⟫} =
          {y : Eucl d | (⟪x k', y⟫ : ℝ) < ⟪x k, y⟫} := by
        ext y; simp [hlt]
      rw [heq2]
      exact measurableSet_lt (f := fun y : Eucl d => (⟪x k', y⟫ : ℝ))
        (g := fun y : Eucl d => (⟪x k, y⟫ : ℝ)) (by fun_prop) (by fun_prop)
    · show MeasurableSet {y : Eucl d | k' < k → (⟪x k', y⟫ : ℝ) < ⟪x k, y⟫}
      have heq2 : {y : Eucl d | k' < k → (⟪x k', y⟫ : ℝ) < ⟪x k, y⟫} = Set.univ := by
        ext y; simp [hlt]
      rw [heq2]
      exact MeasurableSet.univ

/-- **The tie-broken cells exactly partition the sphere's mass.** For any sphere-supported
probability measure, the cell masses sum to `1` -- the finite-additivity glue between
`voronoiCell'_disjoint` (pairwise disjoint) and `voronoiCell'_covers` (covers the sphere) that
`exists_deficit_routing`'s balanced-supply/demand hypothesis needs at its point of use. -/
theorem sum_measure_voronoiCell' {M : ℕ} (hM : 0 < M) (μ : Measure (Eucl d))
    [IsProbabilityMeasure μ] (hμS : μ (sphere d)ᶜ = 0) (x : Fin M → Eucl d) :
    ∑ k, μ (voronoiCell' x k) = 1 := by
  have hmeas : ∀ k, MeasurableSet (voronoiCell' x k) := measurableSet_voronoiCell' x
  have hcompl : μ (⋃ k, voronoiCell' x k)ᶜ = 0 := by
    apply measure_mono_null _ hμS
    intro y hy
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hy
    show y ∉ sphere d
    intro hys
    obtain ⟨k, hk⟩ := voronoiCell'_covers hM x hys
    exact hy k hk
  have hUnion : μ (⋃ k, voronoiCell' x k) = 1 := by
    have hone := prob_add_prob_compl (μ := μ) (MeasurableSet.iUnion hmeas)
    rwa [hcompl, add_zero] at hone
  have hsum := measure_iUnion (μ := μ) (f := voronoiCell' x)
    (fun k k' hne => voronoiCell'_disjoint x hne) hmeas
  rw [hUnion, tsum_fintype] at hsum
  exact hsum.symm

