import Regression.OldStatements
import Regression.Refuted.F12_HeavyTails

/-!
# F26: the re-stated `lemma_3_4_part2` without sphere supports is still false (atomless heavy tails)

Re-derivation of the F12 heavy-tails refutation against the 2026-07-27 non-vacuous re-statement
(finding F26, RESEARCH.md; the re-statement protocol of WORKFLOW.md requires re-deriving the
adapters whenever a guarded statement is deliberately re-stated). The re-statement added
`[NoAtoms μ]` and `hsupp : μ.support = ν.support`, so the historical ATOMIC heavy witnesses
(`heavy r`, sums of Diracs) no longer fit the sphere-free shape; this file rebuilds the
refutation with ATOMLESS heavy-tailed measures.

Witnesses (`d = 1`): `heavyE` is the pushforward to `Eucl 1` of `x ↦ x⁻¹` on the uniform `(0,1)`
(the density-`x⁻²` law on `(1,∞)`: atomless, probability, identity NOT integrable), `unifE` the
pushforward of the uniform `(1,2)` (atomless, bounded). The pair is two MIXTURES of the same two
generators with different weights: `heavyMixMu := (1/2)•heavyE + (1/2)•unifE`,
`heavyMixNu := (1/4)•heavyE + (3/4)•unifE`. The supports then coincide automatically (same
generators, nonzero weights), the mixtures differ (they disagree on `{x | x 0 < 2}`: `3/4` vs
`7/8`), both are non-integrable (junk Bochner barycenter `0`), so the colinearity holds with
`γ = 1/2` (`0 = (1/2) • 0`), and both miss the sphere entirely, so `attnMeasureFlow` is the junk
identity (`attnMeasureFlow_of_compl_sphere_ne_zero`) and the `∀ γ₂` non-colinearity fails at
`γ₂ = 0`.
-/

set_option autoImplicit false

namespace Regression.Refuted

open MeasureTheory MeasureToMeasure MeasureToMeasure.Statements Set
open MeasureToMeasure.Foundations (AttnSchedule attnMeasureFlow)
open MeasureToMeasure.Leaves (barycenter)
open scoped ENNReal

/-! ### The `Eucl 1` embedding of a real random variable -/

theorem atom_eq_smul (r : ℝ) : atom r = r • atom 1 := by
  unfold atom
  refine WithLp.ofLp_injective 2 ?_
  funext i
  fin_cases i
  simp [EuclideanSpace.single]

theorem atom_measurable : Measurable atom := by
  have h : atom = fun r : ℝ => r • atom 1 := funext atom_eq_smul
  rw [h]
  exact (continuous_id.smul continuous_const).measurable

theorem atom_injective : Function.Injective atom := by
  intro a b hab
  have h := congrFun (congrArg (fun (v : Eucl 1) i => v i) hab) 0
  simpa [atom_apply_zero] using h

theorem atom_norm_eq (r : ℝ) : ‖atom r‖ = ‖r‖ := by
  rw [atom_eq_smul, norm_smul, atom_norm zero_le_one, mul_one]

/-! ### The two atomless generators -/

/-- The heavy generator on `ℝ`: pushforward of the uniform `(0,1)` under `x ↦ x⁻¹`, i.e. the
density-`x⁻²` law on `(1,∞)`. -/
noncomputable def heavyBase : Measure ℝ := (volume.restrict (Ioo (0:ℝ) 1)).map (fun x => x⁻¹)

/-- The heavy generator, embedded in `Eucl 1`. -/
noncomputable def heavyE : Measure (Eucl 1) := heavyBase.map atom

/-- The bounded generator: uniform `(1,2)`, embedded in `Eucl 1`. -/
noncomputable def unifE : Measure (Eucl 1) := (volume.restrict (Ioo (1:ℝ) 2)).map atom

instance heavyE_prob : IsProbabilityMeasure heavyE := by
  constructor
  rw [heavyE, Measure.map_apply atom_measurable MeasurableSet.univ, Set.preimage_univ,
    heavyBase, Measure.map_apply measurable_inv MeasurableSet.univ]
  simp [Real.volume_Ioo]

instance unifE_prob : IsProbabilityMeasure unifE := by
  constructor
  rw [unifE, Measure.map_apply atom_measurable MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_apply_univ, Real.volume_Ioo]
  norm_num

theorem heavyBase_singleton (y : ℝ) : heavyBase {y} = 0 := by
  rw [heavyBase, Measure.map_apply measurable_inv (measurableSet_singleton y),
    Measure.restrict_apply' measurableSet_Ioo]
  have hsub : (fun x : ℝ => x⁻¹) ⁻¹' {y} ⊆ {y⁻¹, 0} := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
    rcases eq_or_ne x 0 with rfl | hx0
    · right; rfl
    · left
      rw [← hx, inv_inv]
  refine measure_mono_null (Set.inter_subset_left.trans hsub) ?_
  exact (Set.toFinite _).measure_zero _

theorem heavyE_singleton (y : Eucl 1) : heavyE {y} = 0 := by
  rw [heavyE, Measure.map_apply atom_measurable (measurableSet_singleton y)]
  rcases Set.eq_empty_or_nonempty (atom ⁻¹' {y}) with he | ⟨r, hr⟩
  · rw [he]; simp
  · have hpre : atom ⁻¹' {y} = {r} := by
      ext s
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hr ⊢
      constructor
      · intro hs; exact atom_injective (hs.trans hr.symm)
      · rintro rfl; exact hr
    rw [hpre]
    exact heavyBase_singleton r

theorem unifE_singleton (y : Eucl 1) : unifE {y} = 0 := by
  rw [unifE, Measure.map_apply atom_measurable (measurableSet_singleton y)]
  rcases Set.eq_empty_or_nonempty (atom ⁻¹' {y}) with he | ⟨r, hr⟩
  · rw [he]; simp
  · have hpre : atom ⁻¹' {y} = {r} := by
      ext s
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hr ⊢
      constructor
      · intro hs; exact atom_injective (hs.trans hr.symm)
      · rintro rfl; exact hr
    rw [hpre, Measure.restrict_apply' measurableSet_Ioo]
    exact measure_mono_null Set.inter_subset_left Real.volume_singleton

/-! ### Non-integrability of the heavy generator, transferred through the embedding -/

theorem heavyBase_not_int : ¬ Integrable (fun x : ℝ => x) heavyBase := by
  intro h
  have h0 : Integrable (id : ℝ → ℝ) ((volume.restrict (Ioo (0:ℝ) 1)).map (fun x => x⁻¹)) := h
  have h2 : Integrable (fun x : ℝ => x⁻¹) (volume.restrict (Ioo (0:ℝ) 1)) :=
    (integrable_map_measure aestronglyMeasurable_id measurable_inv.aemeasurable).mp h0
  have hiff : IntegrableOn (fun x : ℝ => x ^ (-1 : ℝ)) (Ioo (0:ℝ) 1) volume := by
    refine (integrableOn_congr_fun (fun x _ => ?_) measurableSet_Ioo).mp h2
    rw [Real.rpow_neg_one]
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff one_pos] at hiff
  norm_num at hiff

theorem heavyE_not_int : ¬ Integrable (fun x : Eucl 1 => x) heavyE := by
  intro h
  have h0 : Integrable (id : Eucl 1 → Eucl 1) (heavyBase.map atom) := h
  have h1 : Integrable atom heavyBase :=
    (integrable_map_measure aestronglyMeasurable_id atom_measurable.aemeasurable).mp h0
  have h2 : Integrable (fun r : ℝ => ‖r‖) heavyBase :=
    h1.norm.congr (Filter.Eventually.of_forall fun r => atom_norm_eq r)
  exact heavyBase_not_int ((integrable_norm_iff aestronglyMeasurable_id).mp h2)

/-! ### The mixtures -/

/-- `μ` of the F26 pair: `(1/2)•heavyE + (1/2)•unifE`. -/
noncomputable def heavyMixMu : Measure (Eucl 1) := (1/2 : ℝ≥0∞) • heavyE + (1/2 : ℝ≥0∞) • unifE

/-- `ν` of the F26 pair: `(1/4)•heavyE + (3/4)•unifE`. -/
noncomputable def heavyMixNu : Measure (Eucl 1) := (1/4 : ℝ≥0∞) • heavyE + (3/4 : ℝ≥0∞) • unifE

instance heavyMixMu_prob : IsProbabilityMeasure heavyMixMu := by
  constructor
  rw [heavyMixMu, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
    smul_eq_mul, measure_univ, measure_univ, mul_one]
  exact ENNReal.add_halves 1

instance heavyMixNu_prob : IsProbabilityMeasure heavyMixNu := by
  constructor
  rw [heavyMixNu, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
    smul_eq_mul, measure_univ, measure_univ, mul_one, mul_one]
  rw [ENNReal.div_add_div_same, show (1:ℝ≥0∞)+3 = 4 by norm_num]
  exact ENNReal.div_self (by norm_num) (by norm_num)

theorem heavyMixNu_singleton (y : Eucl 1) : heavyMixNu {y} = 0 := by
  show ((1/4 : ℝ≥0∞) • heavyE + (3/4 : ℝ≥0∞) • unifE) {y} = 0
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    heavyE_singleton, unifE_singleton]
  simp

instance heavyMixMu_noAtoms : NoAtoms heavyMixMu := by
  constructor
  intro y
  show ((1/2 : ℝ≥0∞) • heavyE + (1/2 : ℝ≥0∞) • unifE) {y} = 0
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    heavyE_singleton, unifE_singleton]
  simp

/-! ### The mixtures differ: they disagree on the half-line `{x | x 0 < 2}` -/

theorem coordLt_measurableSet : MeasurableSet {x : Eucl 1 | x 0 < 2} :=
  measurableSet_lt ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).continuous.measurable)
    measurable_const

theorem atom_preimage_coordLt : atom ⁻¹' {x : Eucl 1 | x 0 < 2} = {r : ℝ | r < 2} := by
  ext r
  simp [atom_apply_zero]

theorem heavyE_coordLt : heavyE {x : Eucl 1 | x 0 < 2} = ENNReal.ofReal (1/2) := by
  rw [heavyE, Measure.map_apply atom_measurable coordLt_measurableSet, atom_preimage_coordLt,
    show {r : ℝ | r < 2} = Set.Iio 2 from rfl, heavyBase,
    Measure.map_apply measurable_inv measurableSet_Iio,
    Measure.restrict_apply' measurableSet_Ioo]
  have hset : (fun x : ℝ => x⁻¹) ⁻¹' Set.Iio 2 ∩ Ioo (0:ℝ) 1 = Ioo (1/2 : ℝ) 1 := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iio, Set.mem_Ioo]
    constructor
    · rintro ⟨hinv, hx0, hx1⟩
      refine ⟨?_, hx1⟩
      have h2 : (2:ℝ)⁻¹ < x := (inv_lt_comm₀ hx0 two_pos).mp hinv
      linarith
    · rintro ⟨hhalf, hx1⟩
      have hx0 : 0 < x := lt_trans (by norm_num) hhalf
      have h2 : (2:ℝ)⁻¹ < x := by linarith
      exact ⟨(inv_lt_comm₀ hx0 two_pos).mpr h2, hx0, hx1⟩
  rw [hset, Real.volume_Ioo]
  norm_num

theorem unifE_coordLt : unifE {x : Eucl 1 | x 0 < 2} = 1 := by
  rw [unifE, Measure.map_apply atom_measurable coordLt_measurableSet, atom_preimage_coordLt,
    Measure.restrict_apply' measurableSet_Ioo]
  have hset : {r : ℝ | r < 2} ∩ Ioo (1:ℝ) 2 = Ioo (1:ℝ) 2 := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ioo]
    constructor
    · rintro ⟨_, h⟩; exact h
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2⟩
  rw [hset, Real.volume_Ioo]
  norm_num

theorem heavyMixMu_ne_heavyMixNu : heavyMixMu ≠ heavyMixNu := by
  intro hEq
  have hμ : heavyMixMu {x : Eucl 1 | x 0 < 2}
      = (1/2 : ℝ≥0∞) * ENNReal.ofReal (1/2) + (1/2 : ℝ≥0∞) * 1 := by
    rw [heavyMixMu, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
      smul_eq_mul, heavyE_coordLt, unifE_coordLt]
  have hν : heavyMixNu {x : Eucl 1 | x 0 < 2}
      = (1/4 : ℝ≥0∞) * ENNReal.ofReal (1/2) + (3/4 : ℝ≥0∞) * 1 := by
    rw [heavyMixNu, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
      smul_eq_mul, heavyE_coordLt, unifE_coordLt]
  rw [hEq, hν] at hμ
  -- `3/4 = 7/8` in `ℝ≥0∞`: contradiction after passing to `toReal`
  rw [show ENNReal.ofReal (1/2 : ℝ) = (1/2 : ℝ≥0∞) by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num] at hμ
  have h' := congrArg ENNReal.toReal hμ
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)] at h'
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one] at h'
  norm_num at h'

/-! ### Support equality (automatic for two mixtures of the same generators) -/

theorem support_smul_eq_e1 {c : ℝ≥0∞} (hc0 : c ≠ 0) (ρ : Measure (Eucl 1)) :
    (c • ρ).support = ρ.support := by
  ext x
  rw [Measure.mem_support_iff_forall, Measure.mem_support_iff_forall]
  constructor
  · intro h U hU
    have hpos := h U hU
    rw [Measure.smul_apply, smul_eq_mul] at hpos
    rw [pos_iff_ne_zero] at hpos ⊢
    intro hcontra
    exact hpos (by rw [hcontra, mul_zero])
  · intro h U hU
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_pos hc0 (h U hU).ne'

theorem heavyMix_support_eq : heavyMixMu.support = heavyMixNu.support := by
  rw [heavyMixMu, heavyMixNu, Measure.support_add, Measure.support_add,
    support_smul_eq_e1 (by norm_num) heavyE, support_smul_eq_e1 (by norm_num) unifE,
    support_smul_eq_e1 (by norm_num) heavyE, support_smul_eq_e1 (by norm_num) unifE]

/-! ### Junk barycenters -/

theorem heavyMixMu_not_int : ¬ Integrable (fun x : Eucl 1 => x) heavyMixMu := by
  intro h
  rw [heavyMixMu] at h
  have h1 : Integrable (fun x : Eucl 1 => x) ((1/2 : ℝ≥0∞) • heavyE) :=
    (integrable_add_measure.mp h).1
  exact heavyE_not_int
    ((integrable_smul_measure (c := (1/2 : ℝ≥0∞)) (by norm_num) (by norm_num)).mp h1)

theorem heavyMixNu_not_int : ¬ Integrable (fun x : Eucl 1 => x) heavyMixNu := by
  intro h
  rw [heavyMixNu] at h
  have h1 : Integrable (fun x : Eucl 1 => x) ((1/4 : ℝ≥0∞) • heavyE) :=
    (integrable_add_measure.mp h).1
  exact heavyE_not_int
    ((integrable_smul_measure (c := (1/4 : ℝ≥0∞)) (by norm_num) (by norm_num)).mp h1)

theorem heavyMixMu_bary_zero : barycenter heavyMixMu = 0 := by
  show (∫ x, x ∂heavyMixMu) = 0
  exact integral_undef heavyMixMu_not_int

theorem heavyMixNu_bary_zero : barycenter heavyMixNu = 0 := by
  show (∫ x, x ∂heavyMixNu) = 0
  exact integral_undef heavyMixNu_not_int

/-! ### Orthant support -/

theorem orthant_one_measurableSet : MeasurableSet (orthant 1) := by
  have h : orthant 1 = ⋂ i : Fin 1, {v : Eucl 1 | 0 < v i} := by
    ext v; simp [orthant, Set.mem_iInter]
  rw [h]
  exact MeasurableSet.iInter fun i =>
    measurableSet_lt measurable_const ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable)

theorem heavyE_orthant : supportedIn heavyE (orthant 1) := by
  show heavyE (orthant 1)ᶜ = 0
  rw [heavyE, Measure.map_apply atom_measurable orthant_one_measurableSet.compl, heavyBase,
    Measure.map_apply measurable_inv (atom_measurable orthant_one_measurableSet.compl),
    Measure.restrict_apply' measurableSet_Ioo]
  have hempty : (fun x : ℝ => x⁻¹) ⁻¹' (atom ⁻¹' (orthant 1)ᶜ) ∩ Ioo (0:ℝ) 1 = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_Ioo,
      Set.mem_empty_iff_false, iff_false, not_and]
    intro hno hx0 _
    exact hno (atom_mem_orthant (by positivity))
  rw [hempty]
  simp

theorem unifE_orthant : supportedIn unifE (orthant 1) := by
  show unifE (orthant 1)ᶜ = 0
  rw [unifE, Measure.map_apply atom_measurable orthant_one_measurableSet.compl,
    Measure.restrict_apply' measurableSet_Ioo]
  have hempty : atom ⁻¹' (orthant 1)ᶜ ∩ Ioo (1:ℝ) 2 = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_Ioo,
      Set.mem_empty_iff_false, iff_false, not_and]
    intro hno hx1 _
    exact hno (atom_mem_orthant (by linarith))
  rw [hempty]
  simp

theorem heavyMixMu_orthant : supportedIn heavyMixMu (orthant 1) := by
  show heavyMixMu (orthant 1)ᶜ = 0
  rw [heavyMixMu, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
    smul_eq_mul, show heavyE (orthant 1)ᶜ = 0 from heavyE_orthant,
    show unifE (orthant 1)ᶜ = 0 from unifE_orthant]
  simp

theorem heavyMixNu_orthant : supportedIn heavyMixNu (orthant 1) := by
  show heavyMixNu (orthant 1)ᶜ = 0
  rw [heavyMixNu, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
    smul_eq_mul, show heavyE (orthant 1)ᶜ = 0 from heavyE_orthant,
    show unifE (orthant 1)ᶜ = 0 from unifE_orthant]
  simp

/-! ### Off-sphere: the junk identity applies -/

theorem sphere_one_sub_pair : MeasureToMeasure.sphere 1 ⊆ {atom 1, atom (-1)} := by
  intro x hx
  simp only [MeasureToMeasure.sphere, Metric.mem_sphere, dist_zero_right] at hx
  have hx0 : |x 0| = 1 := by
    have hnorm : ‖x‖ = Real.sqrt (x 0 ^ 2) := by
      rw [EuclideanSpace.norm_eq]
      congr 1
      simp [Real.norm_eq_abs, sq_abs]
    rw [hnorm, Real.sqrt_sq_eq_abs] at hx
    exact hx
  rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hx0 with h | h
  · left
    refine WithLp.ofLp_injective 2 ?_
    funext i
    fin_cases i
    simpa [atom, EuclideanSpace.single] using h
  · right
    refine WithLp.ofLp_injective 2 ?_
    funext i
    fin_cases i
    simpa [atom, EuclideanSpace.single] using h

theorem heavyMixMu_compl_sphere_ne_zero : heavyMixMu (MeasureToMeasure.sphere 1)ᶜ ≠ 0 := by
  intro h0
  have hzero : heavyMixMu (MeasureToMeasure.sphere 1) = 0 := by
    refine measure_mono_null sphere_one_sub_pair ?_
    have h1 : heavyMixMu {atom 1, atom (-1)} ≤ heavyMixMu {atom 1} + heavyMixMu {atom (-1)} :=
      measure_union_le _ _
    rw [measure_singleton, measure_singleton, add_zero] at h1
    exact le_antisymm h1 zero_le
  have hms : MeasurableSet (MeasureToMeasure.sphere 1) := Metric.isClosed_sphere.measurableSet
  have htotal : heavyMixMu (MeasureToMeasure.sphere 1)
      + heavyMixMu (MeasureToMeasure.sphere 1)ᶜ = 1 :=
    (measure_add_measure_compl hms).trans measure_univ
  rw [hzero, h0, add_zero] at htotal
  exact zero_ne_one htotal

theorem heavyMixNu_compl_sphere_ne_zero : heavyMixNu (MeasureToMeasure.sphere 1)ᶜ ≠ 0 := by
  intro h0
  have hzero : heavyMixNu (MeasureToMeasure.sphere 1) = 0 := by
    refine measure_mono_null sphere_one_sub_pair ?_
    have h1 : heavyMixNu {atom 1, atom (-1)} ≤ heavyMixNu {atom 1} + heavyMixNu {atom (-1)} :=
      measure_union_le _ _
    rw [heavyMixNu_singleton, heavyMixNu_singleton, add_zero] at h1
    exact le_antisymm h1 zero_le
  have hms : MeasurableSet (MeasureToMeasure.sphere 1) := Metric.isClosed_sphere.measurableSet
  have htotal : heavyMixNu (MeasureToMeasure.sphere 1)
      + heavyMixNu (MeasureToMeasure.sphere 1)ᶜ = 1 :=
    (measure_add_measure_compl hms).trans measure_univ
  rw [hzero, h0, add_zero] at htotal
  exact zero_ne_one htotal

/-! ### The disproof -/

/-- F26: the re-stated `lemma_3_4_part2` WITHOUT sphere supports is false: atomless heavy-tailed
orthant mixtures have equal supports and junk-zero colinear barycenters, the flow is the junk
identity off the sphere, and the `∀ γ₂` non-colinearity fails at `γ₂ = 0`. -/
theorem attnLemma34Part2NoSphereNoAtoms_false
    (ax : Regression.AttnLemma34Part2NoSphereNoAtomsSig) : False := by
  have hcol : ∃ γ : ℝ, γ ∈ Set.Ioo (0 : ℝ) 1 ∧
      barycenter heavyMixMu = γ • barycenter heavyMixNu := by
    refine ⟨1/2, Set.mem_Ioo.mpr ⟨by norm_num, by norm_num⟩, ?_⟩
    rw [heavyMixMu_bary_zero, heavyMixNu_bary_zero, smul_zero]
  obtain ⟨θ, hθ⟩ := ax heavyMixMu heavyMixNu heavyMixMu_prob heavyMixNu_prob heavyMixMu_noAtoms
    1 one_pos heavyMixMu_ne_heavyMixNu heavyMixMu_orthant heavyMixNu_orthant hcol
    heavyMix_support_eq
  apply hθ 0
  rw [attnMeasureFlow_of_compl_sphere_ne_zero θ heavyMixMu_compl_sphere_ne_zero,
    attnMeasureFlow_of_compl_sphere_ne_zero θ heavyMixNu_compl_sphere_ne_zero,
    heavyMixMu_bary_zero, heavyMixNu_bary_zero, zero_smul]

end Regression.Refuted
