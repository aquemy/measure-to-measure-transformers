import MeasureToMeasure.Leaves.ExtremalBoundaryPoint

/-!
# The extremal point's outward geodesic cap avoids the support (`lemma_3_4_part2` leaf 7)

The paper's (B.16) needs a local witness: some open (geodesic) ball meets one measure's support but
misses the other's. This leaf supplies the STATIC half of that at `t = 0`: a genuine positive-radius
geodesic neighborhood, centered at the sphere point antipodal to the normalized barycenter, entirely
disjoint from `supp μ0` -- built directly from leaf 5's extremal point (`exists_extremal_support_point`,
`Leaves/ExtremalBoundaryPoint.lean`), with NO further hypotheses.

**Construction.** Let `v := barycenter μ0`, `x0` the point of `supp μ0` minimizing `⟪v, ·⟫` (leaf 5),
and `z := -(‖v‖⁻¹ • v)` the antipodal direction. Set `R := geodesicDist z x0` (positive, since
`⟪v, x0⟫ ≥ 0 > -‖v‖ = ⟪v, z⟫` rules out `x0 = z`). Any `y` within geodesic distance `R` of `z` is
STRICTLY closer to `z` than `x0` is, hence (since `cos` is strictly antitone on `[0, π]`)
`⟪z, y⟫ > ⟪z, x0⟫`, which unwinds (via `⟪z, ·⟫ = -‖v‖⁻¹ ⟪v, ·⟫`) to `⟪v, y⟫ < ⟪v, x0⟫` -- contradicting
`x0`'s minimality if `y ∈ supp μ0`. So `geodesicBall z R` and `supp μ0` are disjoint.

This does NOT need footnote 7's `intrinsicInterior` non-degeneracy hypothesis (`MidLevel.lean:267`,
`hu`) -- that hypothesis is presumably load-bearing for a LATER step of the campaign (propagating this
`t = 0` fact to the flowed-in-time separating ball at `T*`, or excluding the paper's own
measure-zero-geodesic-hull edge case), not for this static exclusion itself.

M3b/mid-level staging: consumed when `lemma_3_4_part2` is discharged; see `Statements/MidLevel.lean`.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Set
open scoped RealInnerProductSpace
open MeasureToMeasure.Statements

variable {d : ℕ}

/-- **The generic outward-cap exclusion.** Given a nonzero direction `v`, a sphere point `x0`
minimizing `⟪v, ·⟫` over a measure's support with `⟪v, x0⟫ ≥ 0`, the geodesic ball centered at `v`'s
antipode, of radius exactly `x0`'s own geodesic distance from that antipode, is entirely disjoint
from the support. -/
theorem exists_geodesicBall_disjoint_support {μ0 : Measure (Eucl d)} [IsProbabilityMeasure μ0]
    {v x0 : Eucl d} (hvpos : 0 < ‖v‖) (hx0sphere : x0 ∈ sphere d)
    (hge : 0 ≤ ⟪v, x0⟫) (hmin : ∀ x ∈ μ0.support, ⟪v, x0⟫ ≤ ⟪v, x⟫) :
    ∃ z ∈ sphere d, ∃ R > 0, geodesicBall z R ∩ μ0.support = ∅ := by
  set z : Eucl d := -(‖v‖⁻¹ • v) with hzdef
  have hznorm : ‖z‖ = 1 := by
    rw [hzdef, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvpos)]
    field_simp
  have hzsphere : z ∈ sphere d := by
    simpa [sphere, dist_eq_norm] using hznorm
  have hinnervz : ⟪v, z⟫ = -‖v‖ := by
    rw [hzdef, inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hx0ne_z : x0 ≠ z := by
    intro h
    rw [h, hinnervz] at hge
    linarith
  have hzx0lt1 : ⟪z, x0⟫ < 1 := by
    have hne : z - x0 ≠ 0 := sub_ne_zero.mpr hx0ne_z.symm
    have hpos : 0 < ‖z - x0‖ ^ 2 := by positivity
    have hpol : ‖z - x0‖ ^ 2 = 2 - 2 * ⟪z, x0⟫ := by
      rw [norm_sub_sq_real, hznorm, norm_eq_one_of_mem_sphere hx0sphere]; ring
    linarith [hpol ▸ hpos]
  set R : ℝ := geodesicDist z x0 with hRdef
  have hRmem : R ∈ Set.Icc (0 : ℝ) Real.pi := geodesicDist_mem_Icc z x0
  have hRpos : 0 < R := by
    rw [hRdef, geodesicDist]
    exact Real.arccos_pos.mpr hzx0lt1
  refine ⟨z, hzsphere, R, hRpos, ?_⟩
  ext y
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hyball hysupp
  obtain ⟨hysphere, hydist⟩ := hyball
  have hstrict : Real.cos R < Real.cos (geodesicDist z y) :=
    Real.strictAntiOn_cos (geodesicDist_mem_Icc z y) hRmem hydist
  have hcosR : Real.cos R = ⟪z, x0⟫ := cos_geodesicDist hzsphere hx0sphere
  have hcosy : Real.cos (geodesicDist z y) = ⟪z, y⟫ := cos_geodesicDist hzsphere hysphere
  rw [hcosR, hcosy] at hstrict
  have e1 : ⟪z, x0⟫ = -(‖v‖⁻¹ * ⟪v, x0⟫) := by rw [hzdef, inner_neg_left, real_inner_smul_left]
  have e2 : ⟪z, y⟫ = -(‖v‖⁻¹ * ⟪v, y⟫) := by rw [hzdef, inner_neg_left, real_inner_smul_left]
  rw [e1, e2] at hstrict
  have hvinv : 0 < ‖v‖⁻¹ := inv_pos.mpr hvpos
  have hlty : ⟪v, y⟫ < ⟪v, x0⟫ := by nlinarith
  exact absurd (hmin y hysupp) (not_le.mpr hlty)

/-- **Assembled with leaf 5.** Any sphere-and-orthant-supported probability measure with `‖barycenter
μ0‖ < 1` has SOME extremal support point whose outward geodesic cap misses the support entirely. -/
theorem exists_extremal_geodesicBall_disjoint_support {μ0 : Measure (Eucl d)}
    [IsProbabilityMeasure μ0] (hμs : μ0 (sphere d)ᶜ = 0) (hμint : Integrable (fun x : Eucl d => x) μ0)
    (hμorth : μ0 (orthant d)ᶜ = 0) (hvlt : ‖barycenter μ0‖ < 1) :
    ∃ x0 ∈ μ0.support, ∃ z ∈ sphere d, ∃ R > 0, geodesicBall z R ∩ μ0.support = ∅ := by
  obtain ⟨x0, hx0supp, _, hmin, hgap⟩ := exists_extremal_support_point hμs hμint hμorth hvlt
  have hvpos : 0 < ‖barycenter μ0‖ := norm_barycenter_pos_of_orthant hμs hμint hμorth
  have hge : 0 ≤ ⟪barycenter μ0, x0⟫ :=
    inner_nonneg_of_orthant (barycenter_mem_orthant hμs hμint hμorth)
      (support_subset_closedOrthant hμorth hx0supp)
  obtain ⟨z, hzsphere, R, hRpos, hdisj⟩ :=
    exists_geodesicBall_disjoint_support (μ0 := μ0) hvpos (support_subset_sphere hμs hx0supp)
      hge hmin
  exact ⟨x0, hx0supp, z, hzsphere, R, hRpos, hdisj⟩

end MeasureToMeasure.Leaves
