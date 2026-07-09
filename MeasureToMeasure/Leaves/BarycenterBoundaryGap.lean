import MeasureToMeasure.Leaves.GeodesicHullConvex
import Mathlib.MeasureTheory.Measure.Support

/-!
# A quantitative boundary point for a colinear-but-unequal barycenter pair (Lemma 3.4 Part 2 leaf 1)

The paper's Appendix B.3 proof of Lemma 3.4 Part 2 (App. B.3, p.36) picks a point `x0` on the
boundary of the geodesic hull `∂conv_g(supp μ0)` to get a quantitative gap
`‖E_μ0[x]‖ − ⟨E_μ0[x],x0⟩²/‖E_μ0[x]‖ ≥ c > 0` driving the local perturbative divergence argument
(the Taylor/Duhamel comparison of two mean-field trajectories starting at `x0`). This leaf gets the
SAME kind of gap without building any new geodesic-hull-boundary machinery: since the colinearity
hypothesis (`barycenter μ0 = γ • barycenter ν0`, `γ ∈ (0,1)`) already forces `‖barycenter μ0‖ < 1`
strictly (via the existing `norm_barycenter_le_one`), and a probability measure whose barycenter has
norm `< 1` cannot be entirely concentrated at its own normalized barycenter direction, there is a
point `x0` in the TOPOLOGICAL SUPPORT of `μ0` (not just its geodesic hull) with
`⟪barycenter μ0, x0⟫ < ‖barycenter μ0‖` — the Cauchy-Schwarz bound is not saturated at `x0`. This is
weaker than "on the boundary of the geodesic hull" but suffices for the pointwise gap the local
divergence argument needs.

M3b/mid-level staging: consumed when `lemma_3_4_part2` is discharged; see
`Statements/MidLevel.lean`.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Set
open scoped RealInnerProductSpace

variable {d : ℕ}

/-- If `⟪u, barycenter μ0⟫ < 1` for a unit vector `u`, the set where `⟪u, x⟫ < 1` has positive
`μ0`-measure — otherwise `⟪u, x⟫ = 1` `μ0`-a.e. (squeezing the a.e. bound `⟪u,x⟫ ≤ 1` from
Cauchy-Schwarz against the a.e. bound `⟪u,x⟫ ≥ 1` from the zero-measure complement), forcing
`⟪u, barycenter μ0⟫ = ∫ ⟪u,x⟫ ∂μ0 = 1`, a contradiction. -/
theorem exists_pos_measure_lt_one_of_inner_lt {μ0 : Measure (Eucl d)} [IsProbabilityMeasure μ0]
    (hμs : μ0 (sphere d)ᶜ = 0) (hμint : Integrable (fun x : Eucl d => x) μ0)
    {u : Eucl d} (husphere : u ∈ sphere d) (hlt : ⟪u, barycenter μ0⟫ < 1) :
    0 < μ0 {x : Eucl d | ⟪u, x⟫ < 1} := by
  by_contra hcon
  have hzero : μ0 {x : Eucl d | ⟪u, x⟫ < 1} = 0 := le_antisymm (not_lt.mp hcon) bot_le
  have hae_ge : ∀ᵐ x ∂μ0, 1 ≤ ⟪u, x⟫ := by
    rw [ae_iff]
    have heqset : {x : Eucl d | ¬ 1 ≤ ⟪u, x⟫} = {x : Eucl d | ⟪u, x⟫ < 1} := by
      ext x; simp
    rw [heqset]; exact hzero
  have hae_le : ∀ᵐ x ∂μ0, ⟪u, x⟫ ≤ 1 := by
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) hμs
    simp only [Set.mem_setOf_eq, not_le] at hx
    simp only [sphere, Metric.mem_sphere, dist_zero_right, Set.mem_compl_iff]
    intro hxnorm
    have hcs := abs_real_inner_le_norm u x
    rw [norm_eq_one_of_mem_sphere husphere, hxnorm] at hcs
    simp only [mul_one] at hcs
    rw [abs_le] at hcs
    linarith [hcs.2]
  have hae_eq : ∀ᵐ x ∂μ0, ⟪u, x⟫ = 1 := by
    filter_upwards [hae_ge, hae_le] with x h1 h2
    linarith
  have hii : Integrable (fun x : Eucl d => ⟪u, x⟫) μ0 := by
    simpa using (innerSL ℝ u).integrable_comp hμint
  have hib : ∫ x, ⟪u, x⟫ ∂μ0 = ⟪u, barycenter μ0⟫ := by
    simpa [barycenter] using (innerSL ℝ u).integral_comp_comm hμint
  have heq1 : ∫ x, ⟪u, x⟫ ∂μ0 = ∫ _x : Eucl d, (1 : ℝ) ∂μ0 := integral_congr_ae hae_eq
  rw [integral_const] at heq1
  simp only [Measure.real_def, measure_univ, ENNReal.toReal_one, one_smul] at heq1
  rw [hib] at heq1
  linarith [hlt, heq1]

/-- **The colinearity hypothesis already forces a strict barycenter-norm bound**, no Dirac-exclusion
argument needed: `‖barycenter μ0‖ = γ · ‖barycenter ν0‖ ≤ γ < 1`. -/
theorem norm_barycenter_colinear_lt_one {μ0 ν0 : Measure (Eucl d)} [IsProbabilityMeasure μ0]
    [IsProbabilityMeasure ν0]
    (hνs : ν0 (sphere d)ᶜ = 0) (hνint : Integrable (fun x : Eucl d => x) ν0)
    {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) (hcol : barycenter μ0 = γ • barycenter ν0) :
    ‖barycenter μ0‖ < 1 := by
  rw [hcol, norm_smul, Real.norm_eq_abs, abs_of_pos hγ.1]
  have hle : ‖barycenter ν0‖ ≤ 1 := norm_barycenter_le_one hνs hνint
  calc γ * ‖barycenter ν0‖ ≤ γ * 1 := by gcongr; exact hγ.1.le
    _ = γ := mul_one γ
    _ < 1 := hγ.2

/-- **The quantitative boundary point.** For a sphere-supported probability measure `μ0` with
`0 < ‖barycenter μ0‖ < 1`, there is a point `x0` in the topological support of `μ0`, on the sphere,
with `⟪barycenter μ0, x0⟫ < ‖barycenter μ0‖` — the Cauchy-Schwarz bound is not saturated at `x0`. -/
theorem exists_support_inner_lt_norm_barycenter {μ0 : Measure (Eucl d)} [IsProbabilityMeasure μ0]
    (hμs : μ0 (sphere d)ᶜ = 0) (hμint : Integrable (fun x : Eucl d => x) μ0)
    (hvpos : 0 < ‖barycenter μ0‖) (hvlt : ‖barycenter μ0‖ < 1) :
    ∃ x0 ∈ μ0.support, x0 ∈ sphere d ∧ ⟪barycenter μ0, x0⟫ < ‖barycenter μ0‖ := by
  set v := barycenter μ0 with hv
  set u := ‖v‖⁻¹ • v with hu
  have husphere : u ∈ sphere d := by
    simp only [sphere, Metric.mem_sphere, dist_zero_right, hu, norm_smul, norm_inv, norm_norm]
    field_simp
  have hinner_v : ⟪u, v⟫ = ‖v‖ := by
    rw [hu, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  have hlt1 : ⟪u, v⟫ < 1 := by rw [hinner_v]; exact hvlt
  have hSpos := exists_pos_measure_lt_one_of_inner_lt hμs hμint husphere hlt1
  obtain ⟨x0, hx0S, hx0supp⟩ := Measure.nonempty_inter_support_of_pos hSpos
  have hsupp_sub_sphere : μ0.support ⊆ sphere d := by
    have hopen : IsOpen (sphere d)ᶜ := Metric.isClosed_sphere.isOpen_compl
    have := Measure.subset_compl_support_of_isOpen hopen hμs
    rwa [compl_subset_comm, compl_compl] at this
  have hx0sphere : x0 ∈ sphere d := hsupp_sub_sphere hx0supp
  refine ⟨x0, hx0supp, hx0sphere, ?_⟩
  have hlt2 : ⟪u, x0⟫ < 1 := hx0S
  have hux0 : ⟪v, x0⟫ = ‖v‖ * ⟪u, x0⟫ := by
    rw [hu, real_inner_smul_left]; field_simp
  rw [hux0]
  calc ‖v‖ * ⟪u, x0⟫ < ‖v‖ * 1 := mul_lt_mul_of_pos_left hlt2 hvpos
    _ = ‖v‖ := mul_one _

end MeasureToMeasure.Leaves
