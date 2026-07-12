import MeasureToMeasure.Foundations.GeodesicConvex
import MeasureToMeasure.Leaves.WassersteinDiracBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# A geodesically convex set contains an explicit finite ball chain between any two of its points
(`prop_2_2` Stage 3, within-cell chaining)

Given a geodesically convex, OPEN set `C` and two non-antipodal points `p, q ∈ C`, the whole
minimizing geodesic arc from `p` to `q` lies in `C` (this is exactly what geodesic convexity means).
Since the arc is compact and `Cᶜ` is closed and disjoint from it, the arc has a uniform positive
margin to `Cᶜ`; discretizing the arc finely enough (in geodesic distance, via the arc-length
parametrization below) turns this into a finite chain of overlapping geodesic balls, each contained
in `C`, matching the `z : ℕ → Eucl d`, `R : ℕ → ℝ` chain-data shape `gated_chainUnion_retention`
needs.

**The parametrization.** `geodesicArc p q θ := cos θ • p + sin θ • geodesicTangent p q`, where
`geodesicTangent p q` is the unit vector orthogonal to `p` in the direction of `q` (the normalized
component of `q` orthogonal to `p`). This is the standard great-circle arc-length parametrization:
`geodesicArc p q 0 = p`, `⟪p, geodesicArc p q θ⟫ = cos θ` so `geodesicDist p (geodesicArc p q θ) = θ`
EXACTLY for `θ ∈ [0, π]` (no need to separately prove monotonicity of a chord-based parametrization),
and `geodesicArc p q (geodesicDist p q) = q`.

**Status: DONE.** `exists_geodesicConvex_arc_chain` assembles the arc-length parametrization, the
uniform margin, and the step-count arithmetic into an explicit finite chain `z : ℕ → Eucl d`,
`Rad : ℕ → ℝ` (`Rad` constant at the uniform margin `R`) with `z 0 = p`, `z n = q`, every ball a
subset of `C`, consecutive balls overlapping, and index-gap-`≥2` balls disjoint -- matching
`gated_chainUnion_retention_bounded`'s (`GatedChainUnion.lean`) hypothesis shape exactly (`K := n`),
so a caller feeds this straight into it.

Getting here needed a genuine detour: the natural target, `gated_chainUnion_retention`, states its
`hchain`/`hdisj` for ALL `k : ℕ`, unbounded -- but the sphere's compactness means no sequence can
maintain a FIXED minimum pairwise separation for infinitely many index-gap-≥2 pairs (a basic packing
fact), so no naturally-extended infinite tail past the real chain's endpoint can satisfy it. Re-reading
`gated_chainUnion_retention`'s own proof showed its induction only ever invokes `hchain k`/`hdisj j
(k+1)` for indices below the CURRENT `K` being proven -- the unbounded `∀ k` in its hypotheses is
stronger than what the proof consumes, the same over-generalization pattern found repeatedly
elsewhere this session. `gated_chainUnion_retention_bounded` restates it with `hchain`/`hdisj` bounded
by the target `K`, proved via the identical induction, which is what `exists_geodesicConvex_arc_chain`
targets here -- no infinite tail needed at all, since the whole chain is finite (`n` balls) by
construction. See the `prop-2-2-steps-2-3-campaign` project notes for the full writeup.

M3b/mid-level staging: Stage 3 of the `prop_2_2` Steps 2-3 campaign, now COMPLETE; see project notes
for Stage 4 (apply `gated_forest_to_target_retention` per piece) next.
-/

namespace MeasureToMeasure.Leaves

open Set MeasureTheory
open scoped RealInnerProductSpace

variable {d : ℕ}

/-- The unit tangent direction at `p` pointing toward `q`: the component of `q` orthogonal to `p`,
normalized. Well-defined (nonzero before normalizing) exactly when `q ≠ p` and `q ≠ -p`. -/
noncomputable def geodesicTangent (p q : Eucl d) : Eucl d :=
  ‖q - ⟪p, q⟫ • p‖⁻¹ • (q - ⟪p, q⟫ • p)

/-- The pre-normalization tangent vector is nonzero, given `p, q ∈ sphere d` and `q ≠ p`, `q ≠ -p`
(Cauchy-Schwarz equality case). -/
theorem geodesicTangent_pre_ne_zero {p q : Eucl d} (hp : p ∈ sphere d) (hq : q ∈ sphere d)
    (hne : q ≠ p) (hne' : q ≠ -p) : q - (⟪p, q⟫ : ℝ) • p ≠ 0 := by
  intro hzero
  have hpn : ‖p‖ = 1 := norm_eq_one_of_mem_sphere hp
  have hqn : ‖q‖ = 1 := norm_eq_one_of_mem_sphere hq
  have heq : q = (⟪p, q⟫ : ℝ) • p := sub_eq_zero.mp hzero
  have hnorm : ‖q‖ = |(⟪p, q⟫ : ℝ)| * ‖p‖ := by
    conv_lhs => rw [heq]
    rw [norm_smul, Real.norm_eq_abs]
  rw [hqn, hpn, mul_one] at hnorm
  have habs : (⟪p, q⟫ : ℝ) = 1 ∨ (⟪p, q⟫ : ℝ) = -1 := (abs_eq (by norm_num)).mp hnorm.symm
  rcases habs with h1 | h1
  · exact hne (by rw [heq, h1, one_smul])
  · exact hne' (by rw [heq, h1, neg_one_smul])

theorem geodesicTangent_mem_sphere {p q : Eucl d} (hp : p ∈ sphere d) (hq : q ∈ sphere d)
    (hne : q ≠ p) (hne' : q ≠ -p) : geodesicTangent p q ∈ sphere d :=
  normalize_mem_sphere (geodesicTangent_pre_ne_zero hp hq hne hne')

theorem inner_geodesicTangent_eq_zero {p : Eucl d} (hp : p ∈ sphere d) (q : Eucl d) :
    (⟪p, geodesicTangent p q⟫ : ℝ) = 0 := by
  rw [geodesicTangent, real_inner_smul_right, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, norm_eq_one_of_mem_sphere hp]
  ring

/-- The great-circle arc-length parametrization from `p` toward `q`: `θ = 0` is `p`, and moving
along `θ` traces the minimizing geodesic at unit angular speed. -/
noncomputable def geodesicArc (p q : Eucl d) (θ : ℝ) : Eucl d :=
  Real.cos θ • p + Real.sin θ • geodesicTangent p q

theorem geodesicArc_mem_sphere {p q : Eucl d} (hp : p ∈ sphere d) (hq : q ∈ sphere d)
    (hne : q ≠ p) (hne' : q ≠ -p) (θ : ℝ) : geodesicArc p q θ ∈ sphere d := by
  have hpn : ‖p‖ = 1 := norm_eq_one_of_mem_sphere hp
  have htn : ‖geodesicTangent p q‖ = 1 :=
    norm_eq_one_of_mem_sphere (geodesicTangent_mem_sphere hp hq hne hne')
  have hort : (⟪p, geodesicTangent p q⟫ : ℝ) = 0 := inner_geodesicTangent_eq_zero hp q
  have hnormsq : ‖geodesicArc p q θ‖ ^ 2 = 1 := by
    rw [geodesicArc, norm_add_sq_real, norm_smul, norm_smul, hpn, htn, mul_one, mul_one,
      Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, real_inner_smul_left,
      real_inner_smul_right, hort, mul_zero, mul_zero]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hval : ‖geodesicArc p q θ‖ = 1 := by
    have h1 : ‖geodesicArc p q θ‖ = Real.sqrt (‖geodesicArc p q θ‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    rw [h1, hnormsq, Real.sqrt_one]
  exact mem_sphere_zero_iff_norm.mpr hval

theorem geodesicArc_zero (p q : Eucl d) : geodesicArc p q 0 = p := by
  simp [geodesicArc]

theorem inner_geodesicArc {p : Eucl d} (hp : p ∈ sphere d) (q : Eucl d) (θ : ℝ) :
    (⟪p, geodesicArc p q θ⟫ : ℝ) = Real.cos θ := by
  rw [geodesicArc, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, norm_eq_one_of_mem_sphere hp, inner_geodesicTangent_eq_zero hp q]
  ring

theorem geodesicDist_geodesicArc {p : Eucl d} (hp : p ∈ sphere d) (q : Eucl d)
    {θ : ℝ} (hθ : θ ∈ Set.Icc 0 Real.pi) :
    geodesicDist p (geodesicArc p q θ) = θ := by
  rw [geodesicDist, inner_geodesicArc hp, Real.arccos_cos hθ.1 hθ.2]

/-- **Two points of the same arc are exactly `|θ2 - θ1|` apart.** The inner-product form: bilinear
expansion collapses to `cos θ1 cos θ2 + sin θ1 sin θ2 = cos(θ2 - θ1)` since `p` and the tangent are
orthonormal. -/
theorem inner_geodesicArc_geodesicArc {p q : Eucl d} (hp : p ∈ sphere d) (hq : q ∈ sphere d)
    (hne : q ≠ p) (hne' : q ≠ -p) (θ1 θ2 : ℝ) :
    (⟪geodesicArc p q θ1, geodesicArc p q θ2⟫ : ℝ) = Real.cos (θ2 - θ1) := by
  have hpn : ‖p‖ = 1 := norm_eq_one_of_mem_sphere hp
  have htn : ‖geodesicTangent p q‖ = 1 :=
    norm_eq_one_of_mem_sphere (geodesicTangent_mem_sphere hp hq hne hne')
  have hort1 : (⟪p, geodesicTangent p q⟫ : ℝ) = 0 := inner_geodesicTangent_eq_zero hp q
  have hort2 : (⟪geodesicTangent p q, p⟫ : ℝ) = 0 := by
    rw [real_inner_comm]; exact hort1
  simp only [geodesicArc, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq, hpn, htn, hort1, hort2]
  rw [Real.cos_sub]
  ring

/-- **Geodesic distance between two points of the same arc is `|θ2 - θ1|`**, when both fall in
`[0, π]` of separation. -/
theorem geodesicDist_geodesicArc_geodesicArc {p q : Eucl d} (hp : p ∈ sphere d) (hq : q ∈ sphere d)
    (hne : q ≠ p) (hne' : q ≠ -p) {θ1 θ2 : ℝ} (hsep : θ2 - θ1 ∈ Set.Icc 0 Real.pi) :
    geodesicDist (geodesicArc p q θ1) (geodesicArc p q θ2) = θ2 - θ1 := by
  rw [geodesicDist, inner_geodesicArc_geodesicArc hp hq hne hne', Real.arccos_cos hsep.1 hsep.2]

theorem geodesicArc_geodesicDist {p q : Eucl d} (hp : p ∈ sphere d) (hq : q ∈ sphere d)
    (hne : q ≠ p) (hne' : q ≠ -p) : geodesicArc p q (geodesicDist p q) = q := by
  set Θ := geodesicDist p q with hΘdef
  have hcosΘ : Real.cos Θ = (⟪p, q⟫ : ℝ) := cos_geodesicDist hp hq
  have hpn : ‖p‖ = 1 := norm_eq_one_of_mem_sphere hp
  have hqn : ‖q‖ = 1 := norm_eq_one_of_mem_sphere hq
  have hprene : q - (⟪p, q⟫ : ℝ) • p ≠ 0 := geodesicTangent_pre_ne_zero hp hq hne hne'
  have hsinsq : Real.sin Θ ^ 2 = ‖q - (⟪p, q⟫ : ℝ) • p‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, hpn, mul_one, Real.norm_eq_abs, sq_abs, hqn,
      real_inner_smul_right, real_inner_comm p q, ← hcosΘ]
    nlinarith [Real.sin_sq_add_cos_sq Θ]
  have hΘrange : Θ ∈ Set.Icc 0 Real.pi := geodesicDist_mem_Icc p q
  have hsinnn : 0 ≤ Real.sin Θ := Real.sin_nonneg_of_nonneg_of_le_pi hΘrange.1 hΘrange.2
  have hsin : Real.sin Θ = ‖q - (⟪p, q⟫ : ℝ) • p‖ := by
    have h1 : Real.sin Θ = Real.sqrt (Real.sin Θ ^ 2) := (Real.sqrt_sq hsinnn).symm
    rw [h1, hsinsq, Real.sqrt_sq (norm_nonneg _)]
  have hnormne : ‖q - (⟪p, q⟫ : ℝ) • p‖ ≠ 0 := norm_ne_zero_iff.mpr hprene
  show Real.cos Θ • p + Real.sin Θ • geodesicTangent p q = q
  rw [geodesicTangent, hsin, smul_smul, mul_inv_cancel₀ hnormne, one_smul, hcosΘ]
  module

theorem continuous_geodesicArc (p q : Eucl d) : Continuous (geodesicArc p q) := by
  unfold geodesicArc
  fun_prop

/-- **The whole open arc lies in `C`.** For `θ` strictly between `0` and `geodesicDist p q`,
`geodesicArc p q θ` is exactly the normalized positive chord combination `a • p + b • q` with
`a = sin(Θ-θ)/sin Θ > 0`, `b = sin θ / sin Θ > 0` (`Θ := geodesicDist p q`), so `GeodesicConvex C`'s
chord-closure gives membership directly. -/
theorem geodesicArc_mem_of_geodesicConvex {C : Set (Eucl d)} (hC : GeodesicConvex C)
    {p q : Eucl d} (hp : p ∈ C) (hq : q ∈ C) (hne : q ≠ p) (hne' : q ≠ -p)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (geodesicDist p q)) : geodesicArc p q θ ∈ C := by
  have hps : p ∈ sphere d := hC.subset_sphere hp
  have hqs : q ∈ sphere d := hC.subset_sphere hq
  set Θ := geodesicDist p q with hΘdef
  have hΘrange : Θ ∈ Set.Icc 0 Real.pi := geodesicDist_mem_Icc p q
  have hθpos := hθ.1
  have hθΘ := hθ.2
  have hθltpi : θ < Real.pi := hθΘ.trans_le hΘrange.2
  have hΘltpi : Θ < Real.pi := by
    by_contra hcon
    push Not at hcon
    have hΘeqpi : Θ = Real.pi := le_antisymm hΘrange.2 hcon
    apply hne'
    have hcosΘ : Real.cos Θ = (⟪p, q⟫ : ℝ) := cos_geodesicDist hps hqs
    rw [hΘeqpi, Real.cos_pi] at hcosΘ
    have hzero : ‖p + q‖ ^ 2 = 0 := by
      rw [norm_add_sq_real, norm_eq_one_of_mem_sphere hps, norm_eq_one_of_mem_sphere hqs, ← hcosΘ]
      ring
    have hz : p + q = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hzero)
    exact eq_neg_of_add_eq_zero_left (add_comm p q ▸ hz)
  have hΘmθltpi : Θ - θ < Real.pi := by linarith
  have hΘmθpos : 0 < Θ - θ := by linarith
  have hsinθpos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθpos hθltpi
  have hsinΘpos : 0 < Real.sin Θ := Real.sin_pos_of_pos_of_lt_pi (hθpos.trans hθΘ) hΘltpi
  have hsinΘmθpos : 0 < Real.sin (Θ - θ) := Real.sin_pos_of_pos_of_lt_pi hΘmθpos hΘmθltpi
  set a : ℝ := Real.sin (Θ - θ) / Real.sin Θ with hadef
  set b : ℝ := Real.sin θ / Real.sin Θ with hbdef
  have hapos : 0 < a := div_pos hsinΘmθpos hsinΘpos
  have hbpos : 0 < b := div_pos hsinθpos hsinΘpos
  have hcosΘ : Real.cos Θ = (⟪p, q⟫ : ℝ) := cos_geodesicDist hps hqs
  have htangent : geodesicTangent p q = (Real.sin Θ)⁻¹ • (q - (⟪p, q⟫ : ℝ) • p) := by
    have hprene : q - (⟪p, q⟫ : ℝ) • p ≠ 0 := geodesicTangent_pre_ne_zero hps hqs hne hne'
    have hsinsq : Real.sin Θ ^ 2 = ‖q - (⟪p, q⟫ : ℝ) • p‖ ^ 2 := by
      rw [norm_sub_sq_real, norm_smul, norm_eq_one_of_mem_sphere hps, mul_one, Real.norm_eq_abs,
        sq_abs, norm_eq_one_of_mem_sphere hqs, real_inner_smul_right, real_inner_comm p q, ← hcosΘ]
      nlinarith [Real.sin_sq_add_cos_sq Θ]
    have hsin : Real.sin Θ = ‖q - (⟪p, q⟫ : ℝ) • p‖ := by
      have h1 : Real.sin Θ = Real.sqrt (Real.sin Θ ^ 2) := (Real.sqrt_sq hsinΘpos.le).symm
      rw [h1, hsinsq, Real.sqrt_sq (norm_nonneg _)]
    rw [geodesicTangent, hsin]
  have hne0 : Real.sin Θ ≠ 0 := hsinΘpos.ne'
  have hcombo : a • p + b • q = geodesicArc p q θ := by
    have hsinsub : Real.sin (Θ - θ) = Real.sin Θ * Real.cos θ - Real.cos Θ * Real.sin θ :=
      Real.sin_sub Θ θ
    have hacoef : a = Real.cos θ - (⟪p, q⟫ : ℝ) * Real.sin θ * (Real.sin Θ)⁻¹ := by
      rw [hadef, hsinsub, hcosΘ]
      field_simp
    rw [geodesicArc, htangent, hacoef, hbdef]
    module
  have hnorm1 : ‖geodesicArc p q θ‖ = 1 :=
    norm_eq_one_of_mem_sphere (geodesicArc_mem_sphere hps hqs hne hne' θ)
  have hmem := hC.2 p hp q hq a b hapos hbpos
  rwa [hcombo, hnorm1, inv_one, one_smul] at hmem

/-- **Uniform positive margin along the arc.** For a geodesically convex `C` that is RELATIVELY
open in the sphere (`C = sphere d ∩ U` for some ambient-open `U` -- `C` itself is NEVER
ambient-open, since it sits inside the sphere, which has empty ambient interior for `d ≥ 1`; the
relevant "complement" is likewise the RELATIVE one, `sphere d \ C`, not the ambient `Cᶜ`, which is
always all of `Eucl d` minus a sliver and hence useless for a margin argument), with `sphere d \ C`
nonempty, and non-antipodal `p, q ∈ C`, some `R ∈ (0, π/4)` works as a ball radius at EVERY point
of the arc (endpoints included): the whole geodesic ball of radius `R` stays in `C`. Compactness of
`[0, geodesicDist p q]` plus continuity and pointwise positivity of `θ ↦ Metric.infDist
(geodesicArc p q θ) (sphere d \ C)` gives a uniform positive AMBIENT margin `η`; the chord ≤ arc
bridge (`norm_sub_le_geodesicDist`) converts this into a GEODESIC radius bound. -/
theorem exists_uniform_margin {C : Set (Eucl d)} (hC : GeodesicConvex C)
    (hCopen : ∃ U : Set (Eucl d), IsOpen U ∧ C = sphere d ∩ U)
    (hCne : (sphere d \ C).Nonempty) {p q : Eucl d} (hp : p ∈ C) (hq : q ∈ C)
    (hne : q ≠ p) (hne' : q ≠ -p) :
    ∃ R : ℝ, R ∈ Set.Ioo 0 (Real.pi / 2) ∧
      ∀ θ ∈ Set.Icc (0 : ℝ) (geodesicDist p q), geodesicBall (geodesicArc p q θ) R ⊆ C := by
  have hps : p ∈ sphere d := hC.subset_sphere hp
  have hqs : q ∈ sphere d := hC.subset_sphere hq
  set Θ := geodesicDist p q with hΘdef
  have hΘnn : 0 ≤ Θ := (geodesicDist_mem_Icc p q).1
  have harc_mem : ∀ θ ∈ Set.Icc (0 : ℝ) Θ, geodesicArc p q θ ∈ C := by
    intro θ hθ
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · rw [← h0, geodesicArc_zero]; exact hp
    · rcases eq_or_lt_of_le hθ.2 with hΘeq | hΘlt
      · rw [hΘeq, hΘdef, geodesicArc_geodesicDist hps hqs hne hne']; exact hq
      · exact geodesicArc_mem_of_geodesicConvex hC hp hq hne hne' ⟨h0, hΘlt⟩
  obtain ⟨U, hUopen, hCU⟩ := hCopen
  have hCclosed : IsClosed (sphere d \ C) := by
    have heq : sphere d \ C = sphere d ∩ Uᶜ := by
      rw [hCU]; ext y; simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_compl_iff]; tauto
    rw [heq]
    exact Metric.isClosed_sphere.inter hUopen.isClosed_compl
  set f : ℝ → ℝ := fun θ => Metric.infDist (geodesicArc p q θ) (sphere d \ C) with hfdef
  have hfcont : ContinuousOn f (Set.Icc 0 Θ) :=
    (Metric.continuous_infDist_pt (sphere d \ C)).comp_continuousOn
      (continuous_geodesicArc p q).continuousOn
  have hfpos : ∀ θ ∈ Set.Icc (0 : ℝ) Θ, 0 < f θ := by
    intro θ hθ
    rw [hfdef]
    have hnotmem : geodesicArc p q θ ∉ sphere d \ C := fun hcon => hcon.2 (harc_mem θ hθ)
    rw [← hCclosed.closure_eq] at hnotmem
    exact (Metric.infDist_pos_iff_notMem_closure hCne).mp hnotmem
  have hcompact : IsCompact (Set.Icc (0 : ℝ) Θ) := isCompact_Icc
  have hIccne : (Set.Icc (0 : ℝ) Θ).Nonempty := ⟨0, le_refl 0, hΘnn⟩
  obtain ⟨θ0, hθ0mem, hθ0min⟩ := hcompact.exists_isMinOn hIccne hfcont
  set η : ℝ := f θ0 with hηdef
  have hηpos : 0 < η := hfpos θ0 hθ0mem
  refine ⟨min η (Real.pi / 4), ⟨lt_min hηpos (by positivity),
    lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_pos])⟩, ?_⟩
  intro θ hθ x hx
  obtain ⟨hxs, hxdist⟩ := hx
  have hxle : ‖geodesicArc p q θ - x‖ ≤ geodesicDist (geodesicArc p q θ) x :=
    norm_sub_le_geodesicDist (hC.subset_sphere (harc_mem θ hθ)) hxs
  have hxlt_min : ‖geodesicArc p q θ - x‖ < min η (Real.pi / 4) := lt_of_le_of_lt hxle hxdist
  have hxlt_η : ‖geodesicArc p q θ - x‖ < η := lt_of_lt_of_le hxlt_min (min_le_left _ _)
  by_contra hxnotC
  have hinfle : Metric.infDist (geodesicArc p q θ) (sphere d \ C) ≤ dist (geodesicArc p q θ) x :=
    Metric.infDist_le_dist_of_mem ⟨hxs, hxnotC⟩
  rw [dist_eq_norm] at hinfle
  have hmin_le : η ≤ f θ := hθ0min hθ
  rw [hfdef] at hmin_le
  linarith

/-- **A valid step count exists.** For `Θ, R > 0`, some `n ≥ 1` makes the step size `Θ/n` land in
the window `[R, 2R)` needed for consecutive balls to overlap while index-gap-≥2 balls stay
disjoint -- EXCEPT when `n = 1` is forced (short arc, `Θ < R`), where only the upper bound
matters (disjointness is vacuous with only two indices). `n = 1` if `Θ < R`; otherwise
`n = ⌊Θ/R⌋₊` (`≥ 1` since `Θ ≥ R`). -/
theorem exists_valid_step_count {Θ R : ℝ} (hΘpos : 0 < Θ) (hRpos : 0 < R) :
    ∃ n : ℕ, 0 < n ∧ Θ / n < 2 * R ∧ (n = 1 ∨ R ≤ Θ / n) := by
  rcases lt_or_ge Θ R with hcase | hcase
  · refine ⟨1, one_pos, ?_, Or.inl rfl⟩
    rw [Nat.cast_one, div_one]
    linarith
  · set n₀ : ℕ := ⌊Θ / R⌋₊ with hn₀def
    have hΘRge1 : (1 : ℝ) ≤ Θ / R := by rw [le_div_iff₀ hRpos]; linarith
    have hn₀pos : 0 < n₀ := Nat.floor_pos.mpr hΘRge1
    have hn₀le : (n₀ : ℝ) ≤ Θ / R := Nat.floor_le (by positivity)
    have hn₀lt : Θ / R < (n₀ : ℝ) + 1 := Nat.lt_floor_add_one (Θ / R)
    refine ⟨n₀, hn₀pos, ?_, Or.inr ?_⟩
    · rw [div_lt_iff₀ (by exact_mod_cast hn₀pos : (0 : ℝ) < (n₀ : ℝ))]
      have h1 : Θ < R * (n₀ : ℝ) + R := by
        rw [div_lt_iff₀ hRpos] at hn₀lt
        nlinarith
      have h2 : (1 : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hn₀pos
      nlinarith
    · rw [le_div_iff₀ (by exact_mod_cast hn₀pos : (0 : ℝ) < (n₀ : ℝ))]
      rw [le_div_iff₀ hRpos] at hn₀le
      linarith

theorem exists_geodesicConvex_arc_chain {C : Set (Eucl d)} (hC : GeodesicConvex C)
    (hCopen : ∃ U : Set (Eucl d), IsOpen U ∧ C = sphere d ∩ U)
    (hCne : (sphere d \ C).Nonempty) {p q : Eucl d} (hp : p ∈ C) (hq : q ∈ C)
    (hne : q ≠ p) (hne' : q ≠ -p) :
    ∃ (n : ℕ) (z : ℕ → Eucl d) (Rad : ℕ → ℝ),
      0 < n ∧ z 0 = p ∧ z n = q ∧
      (∀ k, z k ∈ sphere d) ∧
      (∀ k, Rad k ∈ Set.Ioo 0 (Real.pi / 2)) ∧
      (∀ k, geodesicBall (z k) (Rad k) ⊆ C) ∧
      (∀ k < n, (geodesicBall (z k) (Rad k) ∩ geodesicBall (z (k + 1)) (Rad (k + 1))).Nonempty) ∧
      (∀ j k, j + 2 ≤ k → k ≤ n →
        Disjoint (geodesicBall (z j) (Rad j)) (geodesicBall (z k) (Rad k))) := by
  have hps : p ∈ sphere d := hC.subset_sphere hp
  have hqs : q ∈ sphere d := hC.subset_sphere hq
  have hinnerqp : (⟪q, p⟫ : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := inner_mem_Ioo_of_ne hqs hps hne hne'
  set Θ := geodesicDist p q with hΘdef
  have hΘrange : Θ ∈ Set.Icc 0 Real.pi := geodesicDist_mem_Icc p q
  have hcosΘ : Real.cos Θ = (⟪p, q⟫ : ℝ) := cos_geodesicDist hps hqs
  have hinner : (⟪p, q⟫ : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by
    rw [real_inner_comm q p]
    exact hinnerqp
  have hΘpos : 0 < Θ := by
    rcases hΘrange.1.lt_or_eq with h0 | h0
    · exact h0
    · exfalso
      have hcos1 : Real.cos Θ = 1 := by rw [← h0, Real.cos_zero]
      rw [hcosΘ] at hcos1
      exact absurd hcos1 hinner.2.ne
  have hΘltpi : Θ < Real.pi := by
    rcases hΘrange.2.lt_or_eq with h0 | h0
    · exact h0
    · exfalso
      have hcosm1 : Real.cos Θ = -1 := by rw [h0, Real.cos_pi]
      rw [hcosΘ] at hcosm1
      exact absurd hcosm1 hinner.1.ne'
  obtain ⟨R, hRrange, hRsub⟩ := exists_uniform_margin hC hCopen hCne hp hq hne hne'
  obtain ⟨n, hnpos, hstepUB, hstepLB⟩ := exists_valid_step_count hΘpos hRrange.1
  set s : ℝ := Θ / n with hsdef
  have hspos : 0 < s := by rw [hsdef]; exact div_pos hΘpos (by exact_mod_cast hnpos)
  have hns : (n : ℝ) * s = Θ := by rw [hsdef]; field_simp
  set z : ℕ → Eucl d := fun k => geodesicArc p q (min k n * s) with hzdef
  set Rad : ℕ → ℝ := fun _ => R with hRaddef
  have hz0 : z 0 = p := by simp [hzdef, geodesicArc_zero]
  have hzn : z n = q := by
    have hstep : (n : ℝ) * s = Θ := by
      rw [hsdef]; field_simp
    simp only [hzdef, min_self]
    rw [hstep]
    exact geodesicArc_geodesicDist hps hqs hne hne'
  have hzmem : ∀ k, z k ∈ sphere d := fun k => geodesicArc_mem_sphere hps hqs hne hne' _
  have hRmem : ∀ k, Rad k ∈ Set.Ioo 0 (Real.pi / 2) := fun _ => hRrange
  have hsub : ∀ k, geodesicBall (z k) (Rad k) ⊆ C := by
    intro k
    apply hRsub
    have hmn : (↑(min k n) : ℝ) * s ≤ (n : ℝ) * s := by
      gcongr
      exact_mod_cast min_le_right k n
    have hstep : (n : ℝ) * s = geodesicDist p q := hΘdef ▸ hns
    exact ⟨by positivity, hstep ▸ hmn⟩
  refine ⟨n, z, Rad, hnpos, hz0, hzn, hzmem, hRmem, hsub, ?_, ?_⟩
  · intro k hk
    have hkn : min k n = k := min_eq_left (by omega)
    have hk1n : min (k + 1) n = k + 1 := min_eq_left (by omega)
    have hzk : z k = geodesicArc p q ((k : ℝ) * s) := by simp only [hzdef, hkn]
    have hzk1 : z (k + 1) = geodesicArc p q (((k : ℝ) + 1) * s) := by
      simp only [hzdef, hk1n]; congr 1; push_cast; ring
    refine ⟨geodesicArc p q ((k : ℝ) * s + s / 2),
      ⟨geodesicArc_mem_sphere hps hqs hne hne' _, ?_⟩,
      geodesicArc_mem_sphere hps hqs hne hne' _, ?_⟩
    · show geodesicDist (z k) (geodesicArc p q ((k : ℝ) * s + s / 2)) < R
      rw [hzk]
      have hd := geodesicDist_geodesicArc_geodesicArc hps hqs hne hne'
        (θ1 := (k : ℝ) * s) (θ2 := (k : ℝ) * s + s / 2) (by constructor <;> linarith [hRrange.2])
      linarith [hd]
    · show geodesicDist (z (k + 1)) (geodesicArc p q ((k : ℝ) * s + s / 2)) < R
      rw [hzk1, geodesicDist_comm]
      have hd := geodesicDist_geodesicArc_geodesicArc hps hqs hne hne'
        (θ1 := (k : ℝ) * s + s / 2) (θ2 := ((k : ℝ) + 1) * s) (by constructor <;> linarith [hRrange.2])
      linarith [hd]
  · intro j k hjk hkK
    rcases hstepLB with hn1 | hRs
    · exfalso; omega
    · have hjn : j ≤ n := by omega
      have hjeqmin : min j n = j := min_eq_left hjn
      have hkeqmin : min k n = k := min_eq_left hkK
      have hzj : z j = geodesicArc p q ((j : ℝ) * s) := by simp only [hzdef, hjeqmin]
      have hzk : z k = geodesicArc p q ((k : ℝ) * s) := by simp only [hzdef, hkeqmin]
      rw [Set.disjoint_left]
      intro x hxj hxk
      have hxjd : geodesicDist (z j) x < R := hxj.2
      have hxkd : geodesicDist (z k) x < R := hxk.2
      have htri : geodesicDist (z j) (z k) ≤ geodesicDist (z j) x + geodesicDist x (z k) :=
        geodesicDist_triangle (hzmem j) hxj.1 (hzmem k)
      have hxkd' : geodesicDist x (z k) < R := by rw [geodesicDist_comm]; exact hxkd
      have hlt2R : geodesicDist (z j) (z k) < 2 * R := by linarith
      have hjkreal : (j : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast hjk
      have hkjle : (k : ℝ) - (j : ℝ) ≤ (n : ℝ) := by
        have h1 : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkK
        have h2 : (0 : ℝ) ≤ (j : ℝ) := by positivity
        linarith
      have hub : ((k : ℝ) - (j : ℝ)) * s ≤ (n : ℝ) * s := mul_le_mul_of_nonneg_right hkjle hspos.le
      have hub2 : ((k : ℝ) - (j : ℝ)) * s ≤ Θ := by rw [hns] at hub; exact hub
      have hd := geodesicDist_geodesicArc_geodesicArc hps hqs hne hne'
        (θ1 := (j : ℝ) * s) (θ2 := (k : ℝ) * s) (by
          constructor
          · nlinarith [hspos]
          · nlinarith [hub2, hΘltpi])
      rw [hzj, hzk] at hlt2R
      rw [hd] at hlt2R
      nlinarith [hRs]

end MeasureToMeasure.Leaves
