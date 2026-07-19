import MeasureToMeasure.Leaves.BarycenterBoundaryGap
import MeasureToMeasure.Statements.SupportedIn

/-!
# The orthant hypothesis makes leaf 1's boundary-point gap double-sided (Lemma 3.4 Part 2 leaf 3)

Leaf 1 (`BarycenterBoundaryGap.lean`) found a point `x0` in the topological support of a
sphere-supported probability measure `μ0` with `⟪barycenter μ0, x0⟫ < ‖barycenter μ0‖` -- the
Cauchy-Schwarz bound not saturated from ABOVE. The paper's local divergence argument (App. B.3,
p.36) needs the STRONGER quantitative gap `‖E_μ0[x]‖ - ⟪E_μ0[x],x0⟫²/‖E_μ0[x]‖ > 0`, which needs
`⟪barycenter μ0, x0⟫` bounded away from BOTH `‖barycenter μ0‖` and `-‖barycenter μ0‖` -- i.e. `x0`
must not be exactly antipodal to the barycenter direction either, which leaf 1 alone does not rule
out (e.g. a two-atom measure at `±barycenter μ0/‖barycenter μ0‖` makes leaf 1's own construction
return exactly the antipodal point).

This leaf shows the `lemma_3_4_part2` axiom's ORTHANT hypothesis (`supportedIn μ (orthant d)`, not
yet used by leaves 1-2) already rules this out for free, no new hypothesis needed: since the orthant
`{x | ∀ i, 0 < x i}` is convex, both the barycenter `v := barycenter μ0` and any support point `x0`
have (weakly) nonnegative coordinates, forcing `⟪v,x0⟫ = Σᵢ vᵢ·x0ᵢ ≥ 0 > -‖v‖` automatically --
combined with leaf 1's `⟪v,x0⟫ < ‖v‖`, this gives the full double-sided bound
`|⟪v,x0⟫| < ‖v‖`, hence the quantitative gap `‖v‖ - ⟪v,x0⟫²/‖v‖ > 0`.

A byproduct fact worth noting on its own: any sphere-and-orthant-supported probability measure has
a STRICTLY POSITIVE barycenter (`norm_barycenter_pos_of_orthant`) -- every coordinate is the
integral of an a.e.-strictly-positive function against a probability measure, hence strictly
positive, so the barycenter can never vanish. This removes what looked like a possible degenerate
edge case (a zero barycenter, where the `pAlign` field vanishes identically) from consideration.

M3b/mid-level staging: consumed when `lemma_3_4_part2` is discharged; see `Statements/MidLevel.lean`.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Set
open scoped RealInnerProductSpace
open MeasureToMeasure.Statements

variable {d : ℕ}

theorem isOpen_orthant : IsOpen (orthant d) := by
  have heq : orthant d = ⋂ i, {x : Eucl d | 0 < EuclideanSpace.proj i x} := by
    ext x; simp [orthant, EuclideanSpace.proj]
  rw [heq]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt continuous_const (EuclideanSpace.proj i).continuous

/-- The closed nonnegative orthant, the closure of `orthant d`. -/
def closedOrthant (d : ℕ) : Set (Eucl d) := {x | ∀ i, 0 ≤ x i}

theorem isClosed_closedOrthant : IsClosed (closedOrthant d) := by
  have heq : closedOrthant d = ⋂ i, {x : Eucl d | 0 ≤ EuclideanSpace.proj i x} := by
    ext x; simp [closedOrthant, EuclideanSpace.proj]
  rw [heq]
  exact isClosed_iInter (fun i => isClosed_le continuous_const (EuclideanSpace.proj i).continuous)

theorem orthant_subset_closedOrthant : orthant d ⊆ closedOrthant d :=
  fun _ hx i => (hx i).le

theorem abs_coord_le_norm (x : Eucl d) (i : Fin d) : |x i| ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq]
  have h1 : |x i| ^ 2 ≤ ∑ j, ‖x j‖ ^ 2 := by
    have := Finset.single_le_sum (f := fun j => ‖x j‖ ^ 2) (fun j _ => sq_nonneg ‖x j‖)
      (Finset.mem_univ i)
    simpa [Real.norm_eq_abs] using this
  have h2 : |x i| ≤ Real.sqrt (∑ j, ‖x j‖ ^ 2) := by
    rw [← Real.sqrt_sq (abs_nonneg (x i))]
    exact Real.sqrt_le_sqrt h1
  exact h2

/-- Every coordinate of the barycenter is strictly positive: `xᵢ > 0` `μ0`-a.e. (orthant support)
integrates to a strictly positive value over the full-mass probability measure. -/
theorem forall_coord_pos_of_orthant {μ0 : Measure (Eucl d)} [IsProbabilityMeasure μ0]
    (hμs : μ0 (sphere d)ᶜ = 0) (horthant : μ0 (orthant d)ᶜ = 0) (i : Fin d) :
    0 < ∫ x, x i ∂μ0 := by
  have hae : ∀ᵐ x ∂μ0, 0 ≤ x i := by
    filter_upwards [horthant] with x hx
    exact (hx i).le
  have hintg : Integrable (fun x : Eucl d => x i) μ0 := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
      ((EuclideanSpace.proj i).continuous.aestronglyMeasurable)
    filter_upwards [hμs] with x hx
    simp only [sphere, Metric.mem_sphere, dist_zero_right] at hx
    calc ‖x i‖ = |x i| := Real.norm_eq_abs _
      _ ≤ ‖x‖ := abs_coord_le_norm x i
      _ = 1 := hx
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae hae hintg]
  have hfull : μ0 (orthant d) = 1 :=
    (MeasureTheory.mem_ae_iff_prob_eq_one isOpen_orthant.measurableSet).mp horthant
  have hsub : orthant d ⊆ Function.support (fun x : Eucl d => x i) := fun x hx => ne_of_gt (hx i)
  calc (0 : ENNReal) < 1 := by norm_num
    _ = μ0 (orthant d) := hfull.symm
    _ ≤ μ0 (Function.support (fun x : Eucl d => x i)) := measure_mono hsub

theorem barycenter_mem_orthant {μ0 : Measure (Eucl d)} [IsProbabilityMeasure μ0]
    (hμs : μ0 (sphere d)ᶜ = 0) (hμint : Integrable (fun x : Eucl d => x) μ0)
    (horthant : μ0 (orthant d)ᶜ = 0) :
    barycenter μ0 ∈ orthant d := by
  intro i
  have hpos := forall_coord_pos_of_orthant hμs horthant i
  have h0 : (barycenter μ0) i = ∫ x, x i ∂μ0 :=
    ((EuclideanSpace.proj i).integral_comp_comm hμint).symm
  rw [h0]
  exact hpos

/-- **A sphere-and-orthant-supported probability measure has a strictly positive barycenter.**
Removes the "zero barycenter" degenerate edge case (where the `pAlign` field would vanish
identically) from consideration -- it can never arise under `lemma_3_4_part2`'s hypotheses. -/
theorem norm_barycenter_pos_of_orthant {μ0 : Measure (Eucl d)} [IsProbabilityMeasure μ0]
    (hμs : μ0 (sphere d)ᶜ = 0) (hμint : Integrable (fun x : Eucl d => x) μ0)
    (horthant : μ0 (orthant d)ᶜ = 0) :
    0 < ‖barycenter μ0‖ := by
  have hmem := barycenter_mem_orthant hμs hμint horthant
  cases isEmpty_or_nonempty (Fin d) with
  | inl h =>
    exfalso
    have hempty : sphere d = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false, sphere, Metric.mem_sphere, dist_zero_right]
      intro hnorm
      have hx0 : x = 0 := Subsingleton.elim x 0
      rw [hx0, norm_zero] at hnorm
      norm_num at hnorm
    rw [hempty, Set.compl_empty] at hμs
    have hu := measure_univ (μ := μ0)
    rw [hμs] at hu
    exact one_ne_zero hu.symm
  | inr h =>
    obtain ⟨i⟩ := h
    have hne : barycenter μ0 ≠ 0 := by
      intro hz
      have := hmem i
      rw [hz] at this
      simp at this
    exact norm_pos_iff.mpr hne

/-- The topological support of an orthant-supported measure lies in the CLOSED orthant (allowing
zero coordinates at the boundary, unlike `orthant d` itself). -/
theorem support_subset_closedOrthant {μ0 : Measure (Eucl d)}
    (horthant : μ0 (orthant d)ᶜ = 0) :
    μ0.support ⊆ closedOrthant d := by
  have hnull : μ0 (closedOrthant d)ᶜ = 0 :=
    measure_mono_null (Set.compl_subset_compl.mpr orthant_subset_closedOrthant) horthant
  have := Measure.subset_compl_support_of_isOpen isClosed_closedOrthant.isOpen_compl hnull
  rwa [compl_subset_comm, compl_compl] at this

theorem inner_nonneg_of_orthant {v x0 : Eucl d} (hv : v ∈ orthant d) (hx0 : x0 ∈ closedOrthant d) :
    0 ≤ ⟪v, x0⟫ := by
  rw [PiLp.inner_apply]
  apply Finset.sum_nonneg
  intro i _
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  exact mul_nonneg (hx0 i) (hv i).le

/-- **The quantitative double-sided gap.** Leaf 1's boundary point `x0` and the orthant hypothesis
together give the genuine Cauchy-Schwarz gap `‖v‖ - ⟪v,x0⟫²/‖v‖ > 0` the paper's local divergence
argument needs -- no antipodal degeneracy is possible, since `⟪v,x0⟫ ≥ 0` (orthant) beats leaf 1's
`⟪v,x0⟫ < ‖v‖` on the other side. -/
theorem exists_orthant_support_gap {μ0 : Measure (Eucl d)} [IsProbabilityMeasure μ0]
    (hμs : μ0 (sphere d)ᶜ = 0) (hμint : Integrable (fun x : Eucl d => x) μ0)
    (horthant : μ0 (orthant d)ᶜ = 0) (hvlt : ‖barycenter μ0‖ < 1) :
    ∃ x0 ∈ μ0.support, x0 ∈ sphere d ∧
      0 < ‖barycenter μ0‖ - ⟪barycenter μ0, x0⟫ ^ 2 / ‖barycenter μ0‖ := by
  have hvpos := norm_barycenter_pos_of_orthant hμs hμint horthant
  obtain ⟨x0, hx0supp, hx0sphere, hlt⟩ :=
    exists_support_inner_lt_norm_barycenter hμs hμint hvpos hvlt
  refine ⟨x0, hx0supp, hx0sphere, ?_⟩
  have hx0orth : x0 ∈ closedOrthant d := support_subset_closedOrthant horthant hx0supp
  have hvorth : barycenter μ0 ∈ orthant d := barycenter_mem_orthant hμs hμint horthant
  have hge : 0 ≤ ⟪barycenter μ0, x0⟫ := inner_nonneg_of_orthant hvorth hx0orth
  have hsq : ⟪barycenter μ0, x0⟫ ^ 2 < ‖barycenter μ0‖ ^ 2 := sq_lt_sq' (by linarith) hlt
  have hgap : ⟪barycenter μ0, x0⟫ ^ 2 / ‖barycenter μ0‖ < ‖barycenter μ0‖ := by
    rw [div_lt_iff₀ hvpos]
    calc ⟪barycenter μ0, x0⟫ ^ 2 < ‖barycenter μ0‖ ^ 2 := hsq
      _ = ‖barycenter μ0‖ * ‖barycenter μ0‖ := sq (‖barycenter μ0‖)
  linarith

end MeasureToMeasure.Leaves
