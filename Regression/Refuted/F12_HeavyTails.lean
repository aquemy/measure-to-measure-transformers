import Regression.OldStatements
import Regression.Refuted.F12_Volume

/-!
# F12: `lemma_3_4_part1`/`part2` without sphere support are false (heavy tails)

`orthant d` is the AMBIENT positive orthant; without sphere support, heavy-tailed probability
measures are admissible. Their Bochner barycenters are the junk value `0` (the identity is not
integrable), and every linear flow map has bounded displacement, so all flowed barycenters stay
`0`: part 1 then asserts `x ≠ x` and part 2 `¬ SameRay ℝ 0 0`. Repaired in PR #66 (finding F12).

Witnesses (`d = 1`): `heavy r = ∑ₙ 2^{-(n+1)} δ_{r·2^{n+1}·e₀}` for `r = 1, 3` -- probability
measures on the ambient orthant with non-integrable identity, distinct (they disagree on
`{2·e₀}`).

On the mean-field layer (`oldAttnLemma34Part2NoSphere_false`) the argument is even shorter:
heavy measures are not sphere-supported, so `attnMeasureFlow` is the junk identity and the
barycenters never move.
-/

set_option autoImplicit false

namespace Regression.Refuted

open MeasureTheory MeasureToMeasure MeasureToMeasure.Axioms MeasureToMeasure.Statements
open MeasureToMeasure.Foundations (AttnSchedule attnMeasureFlow)
open MeasureToMeasure.Leaves (barycenter)
open scoped ENNReal

/-! ### Step 1: every linear schedule flow map has bounded displacement -/

/-- A single block's field is globally bounded by `b.bound`, so its time-`t` flow moves any
point by at most `b.bound * t` (mean value inequality along the curve). -/
theorem blockFlow_displacement {d : ℕ} (b : Block d) {t : ℝ} (ht : 0 ≤ t) (x : Eucl d) :
    ‖b.blockFlow t x - x‖ ≤ (b.bound : ℝ) * t := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := b.blockCurve x) (f' := fun s => b.field (b.blockCurve x s)) (C := (b.bound : ℝ))
    (s := Set.Icc 0 t)
    (fun s _ => (b.blockCurve_isIntegralCurve x s).hasDerivWithinAt)
    (fun s _ => b.field_le _)
    (convex_Icc 0 t) (Set.left_mem_Icc.mpr ht) (Set.right_mem_Icc.mpr ht)
  rw [b.blockCurve_zero] at h
  have ht' : ‖t - (0 : ℝ)‖ = t := by
    rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg ht]
  rw [ht'] at h
  exact h

/-- Schedule displacement bound: a composition of finitely many bounded-displacement maps has
bounded displacement. -/
theorem flowMap_displacement {d : ℕ} (θ : Params d) {t : ℝ} (ht : 0 ≤ t) :
    ∃ C : ℝ, ∀ x, ‖flowMap θ t x - x‖ ≤ C := by
  induction θ with
  | nil => exact ⟨0, fun x => by simp⟩
  | cons b θ ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨C + (b.bound : ℝ) * t, fun x => ?_⟩
    have hx : flowMap (b :: θ) t x = flowMap θ t (b.blockFlow t x) := rfl
    rw [hx]
    have hsplit : flowMap θ t (b.blockFlow t x) - x
        = (flowMap θ t (b.blockFlow t x) - b.blockFlow t x) + (b.blockFlow t x - x) := by
      abel
    rw [hsplit]
    exact (norm_add_le _ _).trans
      (add_le_add (hC (b.blockFlow t x)) (blockFlow_displacement b ht x))

/-! ### Step 2: bounded-displacement pushforward preserves non-integrability -/

/-- If the identity is not `μ`-integrable and `f` moves points by at most `C`, the identity is
not integrable for the pushforward `μ.map f` either. -/
theorem not_integrable_id_map {d : ℕ} (μ : Measure (Eucl d)) [IsFiniteMeasure μ]
    (hμ : ¬ Integrable (id : Eucl d → Eucl d) μ)
    {f : Eucl d → Eucl d} (hf : Measurable f) {C : ℝ} (hC : ∀ x, ‖f x - x‖ ≤ C) :
    ¬ Integrable (id : Eucl d → Eucl d) (μ.map f) := by
  intro h
  rw [integrable_map_measure aestronglyMeasurable_id hf.aemeasurable] at h
  have h1 : Integrable f μ := h
  apply hμ
  have hg : Integrable (fun x : Eucl d => ‖f x‖ + C) μ := h1.norm.add (integrable_const C)
  refine hg.mono' aestronglyMeasurable_id (Filter.Eventually.of_forall fun x => ?_)
  show ‖x‖ ≤ ‖f x‖ + C
  have hxeq : x = f x - (f x - x) := by abel
  calc ‖x‖ = ‖f x - (f x - x)‖ := by rw [← hxeq]
    _ ≤ ‖f x‖ + ‖f x - x‖ := norm_sub_le _ _
    _ ≤ ‖f x‖ + C := add_le_add le_rfl (hC x)

/-! ### Step 3: heavy-tailed probability measures on the ambient orthant (`d = 1`) -/

/-- The point `r · e₀` of `ℝ^1`. -/
noncomputable def atom (r : ℝ) : Eucl 1 := EuclideanSpace.single (0 : Fin 1) r

/-- Coordinate of an atom. -/
theorem atom_apply_zero (r : ℝ) : atom r (0 : Fin 1) = r := by
  simp [atom]

/-- Norm of a nonnegative atom. -/
theorem atom_norm {r : ℝ} (hr : 0 ≤ r) : ‖atom r‖ = r := by
  simp [atom, Real.norm_eq_abs, abs_of_nonneg hr]

/-- Positive atoms lie in the ambient orthant. -/
theorem atom_mem_orthant {r : ℝ} (hr : 0 < r) : atom r ∈ orthant 1 := by
  simp only [orthant, Set.mem_setOf_eq]
  intro i
  rw [Subsingleton.elim i (0 : Fin 1), atom_apply_zero]
  exact hr

/-- The ambient orthant of `Eucl 1` is measurable. -/
theorem measurableSet_orthant1 : MeasurableSet (orthant 1) := by
  have heq : orthant 1
      = (⇑(EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)) : Eucl 1 → ℝ) ⁻¹' Set.Ioi 0 := by
    ext x
    simp only [orthant, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioi]
    constructor
    · intro hx
      simpa using hx 0
    · intro hx i
      rw [Subsingleton.elim i (0 : Fin 1)]
      simpa using hx
  rw [heq]
  exact (isOpen_Ioi.preimage (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).continuous).measurableSet

/-- The geometric weights `2^{-(n+1)}`. -/
noncomputable def w (n : ℕ) : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ (n + 1))⁻¹

/-- The geometric weights sum to `1`. -/
theorem tsum_w : ∑' n, w n = 1 := by
  simp only [w, ENNReal.inv_pow]
  rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top

/-- The heavy-tailed measure with atoms at `r · 2^{n+1} · e₀` and masses `2^{-(n+1)}`. -/
noncomputable def heavy (r : ℝ) : Measure (Eucl 1) :=
  Measure.sum (fun n : ℕ => w n • Measure.dirac (atom (r * 2 ^ (n + 1))))

/-- Evaluation of the heavy measure on a measurable set. -/
theorem heavy_apply (r : ℝ) {s : Set (Eucl 1)} (hs : MeasurableSet s) :
    heavy r s = ∑' n, w n * Measure.dirac (atom (r * 2 ^ (n + 1))) s := by
  simp only [heavy]
  rw [Measure.sum_apply _ hs]
  simp only [Measure.smul_apply, smul_eq_mul]

instance heavy_prob (r : ℝ) : IsProbabilityMeasure (heavy r) := by
  constructor
  rw [heavy_apply r MeasurableSet.univ]
  simp only [measure_univ, mul_one]
  exact tsum_w

/-- The heavy measure is supported in the ambient orthant. -/
theorem heavy_supported {r : ℝ} (hr : 0 < r) : supportedIn (heavy r) (orthant 1) := by
  show heavy r (orthant 1)ᶜ = 0
  rw [heavy_apply r measurableSet_orthant1.compl]
  refine ENNReal.tsum_eq_zero.mpr fun n => ?_
  have hmem : atom (r * 2 ^ (n + 1)) ∈ orthant 1 := atom_mem_orthant (by positivity)
  rw [Measure.dirac_apply' _ measurableSet_orthant1.compl,
    Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hmem), mul_zero]

/-- The identity has infinite first moment against the heavy measure. -/
theorem heavy_lintegral_top {r : ℝ} (hr : 1 ≤ r) :
    ∫⁻ x, ‖x‖ₑ ∂(heavy r) = ⊤ := by
  have h0r : (0 : ℝ) ≤ r := zero_le_one.trans hr
  simp only [heavy]
  rw [lintegral_sum_measure]
  have hterm : ∀ n : ℕ,
      (∫⁻ x, ‖x‖ₑ ∂(w n • Measure.dirac (atom (r * 2 ^ (n + 1)))))
        = w n * ENNReal.ofReal (r * 2 ^ (n + 1)) := by
    intro n
    rw [lintegral_smul_measure, lintegral_dirac, ← ofReal_norm,
      atom_norm (mul_nonneg h0r (by positivity)), smul_eq_mul]
  simp only [hterm]
  refine top_unique ?_
  have hone : ∀ n : ℕ, (1 : ℝ≥0∞) ≤ w n * ENNReal.ofReal (r * 2 ^ (n + 1)) := by
    intro n
    have hpow : ENNReal.ofReal ((2 : ℝ) ^ (n + 1)) = (2 : ℝ≥0∞) ^ (n + 1) := by
      rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hofreal : ((2 : ℝ≥0∞) ^ (n + 1)) ≤ ENNReal.ofReal (r * 2 ^ (n + 1)) := by
      rw [ENNReal.ofReal_mul h0r, hpow]
      conv_lhs => rw [← one_mul ((2 : ℝ≥0∞) ^ (n + 1))]
      gcongr
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hr
    have hcancel : w n * ((2 : ℝ≥0∞) ^ (n + 1)) = 1 := by
      simp only [w]
      exact ENNReal.inv_mul_cancel (pow_ne_zero _ two_ne_zero)
        (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
    calc (1 : ℝ≥0∞) = w n * ((2 : ℝ≥0∞) ^ (n + 1)) := hcancel.symm
      _ ≤ w n * ENNReal.ofReal (r * 2 ^ (n + 1)) := by gcongr
  calc (⊤ : ℝ≥0∞) = ∑' _ : ℕ, (1 : ℝ≥0∞) :=
        (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
    _ ≤ ∑' n, w n * ENNReal.ofReal (r * 2 ^ (n + 1)) := ENNReal.tsum_le_tsum hone

/-- The identity is not Bochner-integrable against the heavy measure. -/
theorem heavy_not_integrable {r : ℝ} (hr : 1 ≤ r) :
    ¬ Integrable (fun x : Eucl 1 => x) (heavy r) := by
  intro h
  have hfin : (∫⁻ x, ‖x‖ₑ ∂(heavy r)) < ⊤ := h.hasFiniteIntegral
  rw [heavy_lintegral_top hr] at hfin
  exact lt_irrefl _ hfin

/-- The two heavy witnesses are distinct measures (they disagree on `{2·e₀}`). -/
theorem heavy_one_ne_heavy_three : heavy 1 ≠ heavy 3 := by
  intro h
  have h3 : heavy 3 {atom 2} = 0 := by
    rw [heavy_apply 3 (measurableSet_singleton _)]
    refine ENNReal.tsum_eq_zero.mpr fun n => ?_
    have hne : atom ((3 : ℝ) * 2 ^ (n + 1)) ∉ ({atom 2} : Set (Eucl 1)) := by
      simp only [Set.mem_singleton_iff]
      intro heq
      have happ := congrArg (fun v : Eucl 1 => v (0 : Fin 1)) heq
      simp only [atom_apply_zero] at happ
      have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
      have hps : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := pow_succ' 2 n
      linarith
    rw [Measure.dirac_apply' _ (measurableSet_singleton _),
      Set.indicator_of_notMem hne, mul_zero]
  have h1 : (2 : ℝ≥0∞)⁻¹ ≤ heavy 1 {atom 2} := by
    rw [heavy_apply 1 (measurableSet_singleton _)]
    have hle := ENNReal.le_tsum
      (f := fun n : ℕ => w n * Measure.dirac (atom ((1 : ℝ) * 2 ^ (n + 1))) {atom 2}) 0
    refine le_trans (le_of_eq ?_) hle
    show (2 : ℝ≥0∞)⁻¹ = w 0 * Measure.dirac (atom ((1 : ℝ) * 2 ^ (0 + 1))) {atom 2}
    have hval : ((1 : ℝ) * 2 ^ (0 + 1)) = 2 := by norm_num
    rw [hval, Measure.dirac_apply_of_mem (Set.mem_singleton_iff.mpr rfl), mul_one]
    simp [w]
  rw [h, h3] at h1
  simp at h1

/-! ### Step 4: all barycenters are the junk value `0` -/

/-- The Bochner barycenter of a heavy measure is the junk value `0`. -/
theorem heavy_barycenter_zero {r : ℝ} (hr : 1 ≤ r) : barycenter (heavy r) = 0 := by
  show (∫ x, x ∂(heavy r)) = 0
  exact integral_undef (heavy_not_integrable hr)

/-- Flowed heavy measures keep the junk barycenter `0` (bounded displacement preserves
non-integrability). -/
theorem flowed_barycenter_zero {d : ℕ} (μ : Measure (Eucl d)) [IsFiniteMeasure μ]
    (hμ : ¬ Integrable (fun x : Eucl d => x) μ) (θ : Params d) {T : ℝ} (hT : 0 ≤ T) :
    barycenter (measureFlow θ T μ) = 0 := by
  obtain ⟨C, hC⟩ := flowMap_displacement θ hT
  have hni : ¬ Integrable (fun x : Eucl d => x) (μ.map (flowMap θ T)) :=
    not_integrable_id_map μ hμ (MeasureToMeasure.measurable_flowMap θ hT) hC
  show (∫ x, x ∂(measureFlow θ T μ)) = 0
  exact integral_undef hni

/-- The heavy measure has all its mass off the unit sphere (its atoms have norm `≥ 2`). -/
theorem heavy_compl_sphere_ne_zero {r : ℝ} (hr : 1 ≤ r) :
    heavy r (MeasureToMeasure.sphere 1)ᶜ ≠ 0 := by
  have hms : MeasurableSet (MeasureToMeasure.sphere 1)ᶜ :=
    (Metric.isClosed_sphere (x := (0 : Eucl 1)) (ε := 1)).measurableSet.compl
  intro h0
  rw [heavy_apply r hms] at h0
  have hk0 := ENNReal.tsum_eq_zero.mp h0 0
  have hmem : atom (r * 2 ^ (0 + 1)) ∈ (MeasureToMeasure.sphere 1)ᶜ := by
    simp only [MeasureToMeasure.sphere, Set.mem_compl_iff, Metric.mem_sphere,
      dist_zero_right]
    rw [atom_norm (by positivity)]
    intro heq
    norm_num at heq
    linarith
  rw [Measure.dirac_apply' _ hms, Set.indicator_of_mem hmem, Pi.one_apply, mul_one] at hk0
  exact absurd hk0 (by simp [w])

/-! ### Step 5: the disproofs -/

/-- F12: `lemma_3_4_part1` without sphere support is false (heavy-tailed junk barycenters). -/
theorem oldLemma34Part1Orthant_false (ax : Regression.OldLemma34Part1OrthantSig) : False := by
  have hbar : barycenter (heavy 1) = barycenter (heavy 3) := by
    rw [heavy_barycenter_zero le_rfl, heavy_barycenter_zero (by norm_num : (1 : ℝ) ≤ 3)]
  obtain ⟨θ, hθ⟩ := ax (heavy 1) (heavy 3) (heavy_prob 1) (heavy_prob 3) 1 one_pos
    heavy_one_ne_heavy_three (heavy_supported one_pos)
    (heavy_supported (by norm_num : (0 : ℝ) < 3)) hbar
  exact hθ (by
    rw [flowed_barycenter_zero (heavy 1) (heavy_not_integrable le_rfl) θ zero_le_one,
      flowed_barycenter_zero (heavy 3) (heavy_not_integrable (by norm_num : (1 : ℝ) ≤ 3)) θ
        zero_le_one])

/-- F12 (mean-field layer): `lemma_3_4_part2` without sphere supports is false -- heavy
measures are non-conforming, so the flow is the junk identity and both barycenters stay at the
junk value `0`, where `SameRay` holds reflexively. -/
theorem oldAttnLemma34Part2NoSphere_false
    (ax : Regression.OldAttnLemma34Part2NoSphereSig) : False := by
  have hcol : ∃ γ : ℝ, γ ∈ Set.Ioo (0 : ℝ) 1 ∧
      barycenter (heavy 1) = γ • barycenter (heavy 3) := by
    refine ⟨1 / 2, Set.mem_Ioo.mpr ⟨by norm_num, by norm_num⟩, ?_⟩
    rw [heavy_barycenter_zero le_rfl, heavy_barycenter_zero (by norm_num : (1 : ℝ) ≤ 3),
      smul_zero]
  obtain ⟨θ, hθ⟩ := ax (heavy 1) (heavy 3) (heavy_prob 1) (heavy_prob 3) 1 one_pos
    heavy_one_ne_heavy_three (heavy_supported one_pos)
    (heavy_supported (by norm_num : (0 : ℝ) < 3)) hcol
  apply hθ
  rw [attnMeasureFlow_of_compl_sphere_ne_zero θ (heavy_compl_sphere_ne_zero le_rfl),
    attnMeasureFlow_of_compl_sphere_ne_zero θ
      (heavy_compl_sphere_ne_zero (by norm_num : (1 : ℝ) ≤ 3)),
    heavy_barycenter_zero le_rfl, heavy_barycenter_zero (by norm_num : (1 : ℝ) ≤ 3)]

end Regression.Refuted
