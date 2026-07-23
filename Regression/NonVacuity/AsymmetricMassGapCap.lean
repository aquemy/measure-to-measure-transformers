import Regression.NonVacuity.MidLevel
import MeasureToMeasure.Leaves.AsymmetricMassGapCap

/-!
# Non-vacuity witness for `exists_cap_nu_mass_zero_at_shared_boundary` (`phase4_asymmetric_massgap_cap`, G3)

Every hypothesis of the axiom is instantiated concretely: two mixtures of the SAME two atomless
"generator" measures on `𝕊² ⊂ ℝ³` (`arcMeasure` from `Regression.NonVacuity.MidLevel`, and its
antipodal reflection `negArcMeasure`), with different but colinear-nonzero weighted barycenters,
and `IsMeanFieldFlow` witnesses supplied generically by the banked `exists_meanFieldFlow`.

**The construction.** `arcMeasure` (`A`) is the uniform pushforward of Lebesgue measure on
`[0, π/4]` along the great-circle arc `t ↦ (cos t, sin t, 0)`; `negArcMeasure` (`B := A.map Neg.neg`)
is its antipodal reflection. Both are atomless sphere-supported probability measures. Because `B` is
the image of `A` under negation, `barycenter B = - barycenter A`, and because `A`'s barycenter has
first coordinate `≥ 1/2` (every point of the arc has `cos t ≥ 1/2` for `t ∈ [0, π/4] ⊆ [0, π/3]`,
via `barycenter_mem_of_supportedIn` applied to the closed halfspace `{x | 1/2 ≤ x 0}`),
`barycenter A ≠ 0`.

Mixing `A` and `B` with two DIFFERENT weight pairs summing to `1` gives two probability measures
`wMu0 := (5/8)•A + (3/8)•B` and `wNu0 := (3/4)•A + (1/4)•B` whose supports are AUTOMATICALLY equal
(`Measure.support_add` plus scalar-multiple support-invariance: both mixtures' support is
`A.support ∪ B.support`, regardless of the weights, as long as all four weights are nonzero) --
this is exactly the paper's own Part 2 scoping hypothesis `supp μ0 = supp ν0`. Barycenter linearity
(`integral_add_measure`/`integral_smul_measure`) computes `barycenter wMu0 = (1/4) • barycenter A`
and `barycenter wNu0 = (1/2) • barycenter A`, so `barycenter wMu0 = (1/2) • barycenter wNu0`
(`γ1 = 1/2 ∈ (0,1)`) and `barycenter wNu0 ≠ 0`. `wMu0` is atomless (a nonneg combination of two
atomless measures, since `NoAtoms` transfers along measurable injections and mixtures of `NoAtoms`
measures with finite, nonzero-independent weights stay `NoAtoms`).

`exists_meanFieldFlow` (banked, `Foundations/AttnStepExistence.lean`) supplies `IsMeanFieldFlow`
witnesses `Φμ`/`Φν` for the `pAlign 1 (by norm_num)` block on any sphere-supported probability
datum, closing every remaining hypothesis.
-/

set_option autoImplicit false

namespace Regression.NonVacuity

open MeasureTheory MeasureToMeasure MeasureToMeasure.Leaves MeasureToMeasure.Foundations
open MeasureToMeasure.Statements (supportedIn)
open scoped RealInnerProductSpace ENNReal

/-! ### `negArcMeasure`: the antipodal reflection of `arcMeasure` -/

/-- The antipodal reflection of `arcMeasure`: the pushforward under `x ↦ -x`. -/
noncomputable def negArcMeasure : Measure (Eucl 3) := arcMeasure.map Neg.neg

theorem measurable_neg3 : Measurable (Neg.neg : Eucl 3 → Eucl 3) := measurable_neg

instance negArcMeasure_isProbabilityMeasure : IsProbabilityMeasure negArcMeasure := by
  constructor
  show (arcMeasure.map Neg.neg) Set.univ = 1
  rw [Measure.map_apply measurable_neg3 MeasurableSet.univ]; simp

theorem negArcMeasure_singleton (y : Eucl 3) : negArcMeasure {y} = 0 := by
  show (arcMeasure.map Neg.neg) {y} = 0
  rw [Measure.map_apply measurable_neg3 (measurableSet_singleton y)]
  rcases Set.eq_empty_or_nonempty ((Neg.neg : Eucl 3 → Eucl 3) ⁻¹' {y}) with he | ⟨x, hx⟩
  · rw [he]; simp
  · have heq : (Neg.neg : Eucl 3 → Eucl 3) ⁻¹' {y} = {x} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
      constructor
      · intro hz; exact neg_injective (hz.trans hx.symm)
      · rintro rfl; exact hx
    rw [heq]; exact arcMeasure_atomless x

theorem negArcMeasure_supportedIn_sphere : supportedIn negArcMeasure (sphere 3) := by
  have hms : MeasurableSet (sphere 3)ᶜ :=
    (Metric.isClosed_sphere (x := (0 : Eucl 3)) (ε := 1)).measurableSet.compl
  show (arcMeasure.map Neg.neg) (sphere 3)ᶜ = 0
  rw [Measure.map_apply measurable_neg3 hms]
  have hpre : (Neg.neg : Eucl 3 → Eucl 3) ⁻¹' (sphere 3)ᶜ = (sphere 3)ᶜ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_compl_iff, sphere, Metric.mem_sphere, dist_eq_norm,
      sub_zero, norm_neg]
  rw [hpre]; exact arcMeasure_supportedIn_sphere

theorem barycenter_negArcMeasure : barycenter negArcMeasure = - barycenter arcMeasure := by
  show (∫ x, x ∂(arcMeasure.map Neg.neg)) = - ∫ x, x ∂arcMeasure
  have hmap : (∫ y, y ∂(arcMeasure.map Neg.neg)) = ∫ x, (Neg.neg x : Eucl 3) ∂arcMeasure :=
    integral_map measurable_neg3.aemeasurable aestronglyMeasurable_id
  rw [hmap]; exact integral_neg _

/-! ### `arcMeasure`'s barycenter is nonzero -/

theorem cos_ge_half_of_mem_Icc {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ Real.pi/4) :
    (1:ℝ)/2 ≤ Real.cos t := by
  have h2 : t ≤ Real.pi / 3 := by linarith [Real.pi_pos]
  have hmono : Real.cos (Real.pi/3) ≤ Real.cos t :=
    Real.cos_le_cos_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos]) h2
  rwa [Real.cos_pi_div_three] at hmono

theorem inner_unitE_apply (t : ℝ) : (⟪unitE 3 0, arcPt t⟫ : ℝ) = arcPt t 0 := by
  show (⟪(EuclideanSpace.single (0 : Fin 3) (1:ℝ)), arcPt t⟫ : ℝ) = arcPt t 0
  rw [EuclideanSpace.inner_single_left]; simp

theorem arcMeasure_supportedIn_halfspace :
    supportedIn arcMeasure {x : Eucl 3 | (1:ℝ)/2 ≤ ⟪unitE 3 0, x⟫} := by
  have hms : MeasurableSet {x : Eucl 3 | (1:ℝ)/2 ≤ ⟪unitE 3 0, x⟫}ᶜ := by
    have hcont : Continuous (fun x : Eucl 3 => (⟪unitE 3 0, x⟫ : ℝ)) :=
      continuous_const.inner continuous_id
    exact (isClosed_le continuous_const hcont).measurableSet.compl
  show arcMeasure {x : Eucl 3 | (1:ℝ)/2 ≤ ⟪unitE 3 0, x⟫}ᶜ = 0
  rw [arcMeasure_apply _ hms]
  have hpre : arcPt ⁻¹' {x : Eucl 3 | (1:ℝ)/2 ≤ ⟪unitE 3 0, x⟫}ᶜ ∩
      Set.Icc (0:ℝ) (Real.pi/4) = ∅ := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_setOf_eq, not_le,
      Set.mem_empty_iff_false, iff_false]
    rintro ⟨ht1, ht2⟩
    have hval : (1:ℝ)/2 ≤ ⟪unitE 3 0, arcPt t⟫ := by
      rw [inner_unitE_apply, arcPt_apply_zero]
      exact cos_ge_half_of_mem_Icc ht2.1 ht2.2
    linarith
  rw [hpre]; simp

theorem halfspace_convex (c : ℝ) : Convex ℝ {x : Eucl 3 | c ≤ ⟪unitE 3 0, x⟫} := by
  have heq : {x : Eucl 3 | c ≤ ⟪unitE 3 0, x⟫} = (innerSL ℝ (unitE 3 0)) ⁻¹' (Set.Ici c) := rfl
  rw [heq]; exact (convex_Ici c).linear_preimage (innerSL ℝ (unitE 3 0)).toLinearMap

theorem halfspace_closed (c : ℝ) : IsClosed {x : Eucl 3 | c ≤ ⟪unitE 3 0, x⟫} := by
  have hcont : Continuous (fun x : Eucl 3 => (⟪unitE 3 0, x⟫ : ℝ)) := continuous_const.inner continuous_id
  exact isClosed_le continuous_const hcont

theorem barycenter_arcMeasure_ne_zero : barycenter arcMeasure ≠ 0 := by
  have hmem := barycenter_mem_of_supportedIn
    (integrable_id_of_sphere_support arcMeasure_supportedIn_sphere)
    (halfspace_convex (1/2)) (halfspace_closed (1/2)) arcMeasure_supportedIn_halfspace
  intro hz
  rw [hz] at hmem
  simp only [Set.mem_setOf_eq, inner_zero_right] at hmem
  linarith

/-! ### Two-weight mixtures of `arcMeasure`/`negArcMeasure`, sharing one support -/

theorem support_smul_eq {μ : Measure (Eucl 3)} {c : ℝ≥0∞} (hc0 : c ≠ 0) :
    (c • μ).support = μ.support := by
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

theorem barycenter_mix {μ ν : Measure (Eucl 3)} {c1 c2 : ℝ≥0∞} (hc1 : c1 ≠ ⊤) (hc2 : c2 ≠ ⊤)
    (hμi : Integrable (fun x : Eucl 3 => x) μ) (hνi : Integrable (fun x : Eucl 3 => x) ν) :
    barycenter (c1 • μ + c2 • ν) = c1.toReal • barycenter μ + c2.toReal • barycenter ν := by
  show (∫ x, x ∂(c1 • μ + c2 • ν)) = c1.toReal • (∫ x, x ∂μ) + c2.toReal • (∫ x, x ∂ν)
  rw [integral_add_measure (hμi.smul_measure hc1) (hνi.smul_measure hc2),
    integral_smul_measure, integral_smul_measure]

/-- A two-weight mixture of `arcMeasure` and `negArcMeasure`. -/
noncomputable def mix (c1 c2 : ℝ≥0∞) : Measure (Eucl 3) := c1 • arcMeasure + c2 • negArcMeasure

theorem isProbabilityMeasure_mix {c1 c2 : ℝ≥0∞} (h : c1 + c2 = 1) :
    IsProbabilityMeasure (mix c1 c2) := by
  constructor
  show (c1 • arcMeasure + c2 • negArcMeasure) Set.univ = 1
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    measure_univ, measure_univ, mul_one, mul_one, h]

theorem mix_noAtoms {c1 c2 : ℝ≥0∞} : NoAtoms (mix c1 c2) := by
  constructor
  intro y
  show (c1 • arcMeasure + c2 • negArcMeasure) {y} = 0
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    arcMeasure_atomless y, negArcMeasure_singleton y, mul_zero, mul_zero, add_zero]

theorem mix_supportedIn_sphere {c1 c2 : ℝ≥0∞} : supportedIn (mix c1 c2) (sphere 3) := by
  show (c1 • arcMeasure + c2 • negArcMeasure) (sphere 3)ᶜ = 0
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  rw [show arcMeasure (sphere 3)ᶜ = 0 from arcMeasure_supportedIn_sphere,
      show negArcMeasure (sphere 3)ᶜ = 0 from negArcMeasure_supportedIn_sphere]
  simp

theorem mix_support {c1 c2 : ℝ≥0∞} (hc1 : c1 ≠ 0) (hc2 : c2 ≠ 0) :
    (mix c1 c2).support = arcMeasure.support ∪ negArcMeasure.support := by
  show (c1 • arcMeasure + c2 • negArcMeasure).support = _
  rw [Measure.support_add, support_smul_eq hc1, support_smul_eq hc2]

theorem barycenter_mix' {c1 c2 : ℝ≥0∞} (hc1 : c1 ≠ ⊤) (hc2 : c2 ≠ ⊤) :
    barycenter (mix c1 c2) =
      c1.toReal • barycenter arcMeasure + c2.toReal • barycenter negArcMeasure := by
  show barycenter (c1 • arcMeasure + c2 • negArcMeasure) = _
  exact barycenter_mix hc1 hc2 (integrable_id_of_sphere_support arcMeasure_supportedIn_sphere)
    (integrable_id_of_sphere_support negArcMeasure_supportedIn_sphere)

/-! ### The two witness measures -/

/-- The witness `μ0`: `(5/8)•arcMeasure + (3/8)•negArcMeasure`. -/
noncomputable def wMu0 : Measure (Eucl 3) := mix (5/8) (3/8)

/-- The witness `ν0`: `(3/4)•arcMeasure + (1/4)•negArcMeasure`. -/
noncomputable def wNu0 : Measure (Eucl 3) := mix (3/4) (1/4)

instance wMu0_isProbabilityMeasure : IsProbabilityMeasure wMu0 := isProbabilityMeasure_mix (by
  rw [ENNReal.div_add_div_same, show (5:ℝ≥0∞)+3 = 8 by norm_num]
  exact ENNReal.div_self (by norm_num) (by norm_num))

instance wNu0_isProbabilityMeasure : IsProbabilityMeasure wNu0 := isProbabilityMeasure_mix (by
  rw [ENNReal.div_add_div_same, show (3:ℝ≥0∞)+1 = 4 by norm_num]
  exact ENNReal.div_self (by norm_num) (by norm_num))

instance wMu0_noAtoms : NoAtoms wMu0 := mix_noAtoms

theorem wMu0_supportedIn_sphere : supportedIn wMu0 (sphere 3) := mix_supportedIn_sphere
theorem wNu0_supportedIn_sphere : supportedIn wNu0 (sphere 3) := mix_supportedIn_sphere

theorem wMu0_wNu0_support_eq : wMu0.support = wNu0.support := by
  rw [wMu0, wNu0, mix_support (by norm_num) (by norm_num), mix_support (by norm_num) (by norm_num)]

theorem wMu0_integrable : Integrable (fun x : Eucl 3 => x) wMu0 :=
  integrable_id_of_sphere_support wMu0_supportedIn_sphere

theorem wNu0_integrable : Integrable (fun x : Eucl 3 => x) wNu0 :=
  integrable_id_of_sphere_support wNu0_supportedIn_sphere

theorem wMu0_bary : barycenter wMu0 = (1/4 : ℝ) • barycenter arcMeasure := by
  show barycenter (mix (5/8) (3/8)) = _
  rw [barycenter_mix' (by apply ENNReal.div_ne_top <;> norm_num)
    (by apply ENNReal.div_ne_top <;> norm_num), barycenter_negArcMeasure]
  have h58 : (5/8 : ℝ≥0∞).toReal = 5/8 := by norm_num
  have h38 : (3/8 : ℝ≥0∞).toReal = 3/8 := by norm_num
  rw [h58, h38]; module

theorem wNu0_bary : barycenter wNu0 = (1/2 : ℝ) • barycenter arcMeasure := by
  show barycenter (mix (3/4) (1/4)) = _
  rw [barycenter_mix' (by apply ENNReal.div_ne_top <;> norm_num)
    (by apply ENNReal.div_ne_top <;> norm_num), barycenter_negArcMeasure]
  have h34 : (3/4 : ℝ≥0∞).toReal = 3/4 := by norm_num
  have h14 : (1/4 : ℝ≥0∞).toReal = 1/4 := by norm_num
  rw [h34, h14]; module

theorem wMu0_wNu0_hcol : barycenter wMu0 = (1/2 : ℝ) • barycenter wNu0 := by
  rw [wMu0_bary, wNu0_bary]; module

theorem wNu0_bary_ne_zero : barycenter wNu0 ≠ 0 := by
  rw [wNu0_bary]
  intro h
  rcases smul_eq_zero.mp h with h1 | h1
  · norm_num at h1
  · exact barycenter_arcMeasure_ne_zero h1

/-- **Non-vacuity of `exists_cap_nu_mass_zero_at_shared_boundary`.** Every hypothesis is
satisfiable simultaneously: `wMu0`/`wNu0` are sphere-supported probability measures with the SAME
topological support, `wMu0` atomless, colinear nonzero barycenters (`γ1 = 1/2`), and
`IsMeanFieldFlow` witnesses for the `pAlign 1` block supplied by `exists_meanFieldFlow`. -/
example : True := by
  haveI := wMu0_isProbabilityMeasure
  haveI := wNu0_isProbabilityMeasure
  haveI := wMu0_noAtoms
  obtain ⟨Φμ, hΦμ⟩ := exists_meanFieldFlow (pAlign (1:ℝ) (by norm_num)) wMu0 wMu0_supportedIn_sphere
  obtain ⟨Φν, hΦν⟩ := exists_meanFieldFlow (pAlign (1:ℝ) (by norm_num)) wNu0 wNu0_supportedIn_sphere
  have _h := exists_cap_nu_mass_zero_at_shared_boundary
    wMu0_supportedIn_sphere wNu0_supportedIn_sphere wMu0_wNu0_support_eq
    wMu0_integrable wNu0_integrable
    (γ1 := 1/2) (by norm_num) wMu0_wNu0_hcol wNu0_bary_ne_zero
    (T := 1) one_pos hΦμ hΦν
  trivial

/-- **Non-vacuity of `exists_asymmetric_massgap_cap`.** Same witness data as above (this leaf takes
literally the same hypotheses as the axiom it assembles from): a concrete asymmetric-mass-gap cap
exists for `wMu0`/`wNu0`. -/
example : True := by
  haveI := wMu0_isProbabilityMeasure
  haveI := wNu0_isProbabilityMeasure
  haveI := wMu0_noAtoms
  obtain ⟨Φμ, hΦμ⟩ := exists_meanFieldFlow (pAlign (1:ℝ) (by norm_num)) wMu0 wMu0_supportedIn_sphere
  obtain ⟨Φν, hΦν⟩ := exists_meanFieldFlow (pAlign (1:ℝ) (by norm_num)) wNu0 wNu0_supportedIn_sphere
  have _h := exists_asymmetric_massgap_cap
    wMu0_supportedIn_sphere wNu0_supportedIn_sphere wMu0_wNu0_support_eq
    wMu0_integrable wNu0_integrable
    (γ1 := 1/2) (by norm_num) wMu0_wNu0_hcol wNu0_bary_ne_zero
    (T := 1) one_pos hΦμ hΦν
  trivial

end Regression.NonVacuity
