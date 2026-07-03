import MeasureToMeasure.Leaves.GatedFlow
import MeasureToMeasure.Leaves.GatedCapMass
import MeasureToMeasure.Foundations.SublevelMass

/-!
# Two-cap retention of the amplitude-scaled gated flow (Lemma B.2, discharge steps 5-7)

The final dynamical piece of the `lemma_B_2` discharge. The paper funnels the mass of a cap
`ℬ₀ = B(z₀, R₀)` into its overlap with a second cap `ℬ₁ = B(z₁, R₁)` with a single gated block
(Appendix B, eqs. B.4-B.8). The formal route *recenters the gate at a point of the overlap*:

* pick `ω ∈ ℬ₀ ∩ ℬ₁` and a target radius `r` with the closed cap `B(ω, r) ⊆ ℬ₀ ∩ ℬ₁`
  (triangle inequality, `geodesicDist_triangle`);
* the closed sub-cap of `ℬ₀` at depth `δ` (eq. B.6, `exists_closed_sublevel_mass_ge`, carrying a
  `(1-ε)` fraction of `μ(ℬ₀)`) lies inside the cap `{x ∈ 𝕊 | m ≤ ⟪x,ω⟫}` around `ω`
  (triangle inequality again, `m = cos(d_g(z₀,ω) + δ')`);
* the **self-centered** gated flow at `ω` (`z = ω`), whose monotone logistic coordinate and
  reaching estimate are already kernel-checked (`gatedBlock_reach`, `gatedBlock_mapsTo_cap`),
  drives that cap into `{y | cos r ≤ ⟪y,ω⟫}` -- provided the log-odds budget is met at the fixed
  horizon `T`. The budget is bought with the **amplitude** `A` of `scaledGatedBlock` (the paper's
  parameter-norm freedom `‖θ‖ ~ C/(T·ε)`): `exists_scaledGatedBlock_mapsTo_cap` chooses `A` from
  `T`, the rim level `m`, and the target level.

Composing with the pushforward bridge (`Axioms.le_measureFlow_of_mapsTo`) yields the retention
`(1-ε)·μ(ℬ₀) ≤ (measureFlow θ T μ)(ℬ₀ ∩ ℬ₁)` for the one-block schedule `θ = [scaledGatedBlock …]`,
which is exactly `lemma_B_2` for sub-hemisphere caps over a probability measure.
-/

namespace MeasureToMeasure

open scoped RealInnerProductSpace ENNReal
open Set MeasureTheory

variable {d : ℕ}

/-!
## The scaled gated flow obeys the same logistic ODE, with drift scalar `A · gateFactor`
-/

/-- The gate ODE for a block carrying the amplitude-scaled gated field: `u' = (A·g)·(1 - u²)`. -/
theorem hasDerivAt_inner_scaledFlow {A : ℝ} {z ω : Eucl d} (hω : ω ∈ sphere d) (cosR : ℝ)
    (b : Block d) (hfield : b.field = scaledGatedField A z ω cosR)
    {x : Eucl d} (hx : x ∈ sphere d) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => (⟪b.blockFlow s x, ω⟫ : ℝ))
      ((A * gateFactor z cosR (b.blockFlow t x)) * (1 - ⟪b.blockFlow t x, ω⟫ ^ 2)) t := by
  have hcurve : HasDerivAt (b.blockCurve x) (b.field (b.blockCurve x t)) t :=
    b.blockCurve_isIntegralCurve x t
  have hsph : b.blockCurve x t ∈ sphere d := b.blockFlow_mem_sphere hx ht
  have hvel : b.field (b.blockCurve x t)
      = tangentialProjector (b.blockCurve x t)
          ((A * gateFactor z cosR (b.blockCurve x t)) • ω) := by
    rw [hfield, scaledGatedField_eq_projector_smul]
  exact Leaves.gate_hasDerivAt_inner hcurve hsph hω (A * gateFactor z cosR (b.blockCurve x t)) hvel

/-- `ω` is a fixed point of the scaled gated field. -/
theorem scaledGatedField_pole_eq_zero {A : ℝ} {z ω : Eucl d} (hω : ω ∈ sphere d) (cosR : ℝ) :
    scaledGatedField A z ω cosR ω = 0 := by
  rw [scaledGatedField, gatedField_pole_eq_zero hω, smul_zero]

/-- `-ω` is a fixed point of the scaled gated field. -/
theorem scaledGatedField_neg_pole_eq_zero {A : ℝ} {z ω : Eucl d} (hω : ω ∈ sphere d) (cosR : ℝ) :
    scaledGatedField A z ω cosR (-ω) = 0 := by
  rw [scaledGatedField, gatedField_neg_pole_eq_zero hω, smul_zero]

/-- The scaled flow from `x ≠ ω` never reaches the pole `ω`. -/
theorem scaledFlow_ne_pole {A : ℝ} {z ω : Eucl d} (hω : ω ∈ sphere d) (cosR : ℝ)
    (b : Block d) (hfield : b.field = scaledGatedField A z ω cosR)
    {x : Eucl d} (hx : x ≠ ω) (t : ℝ) : b.blockFlow t x ≠ ω := by
  intro hcontra
  have hfix : b.blockFlow t ω = ω :=
    b.blockFlow_fixed (by rw [hfield]; exact scaledGatedField_pole_eq_zero hω cosR) t
  exact hx (b.blockFlow_injective t (hcontra.trans hfix.symm))

/-- The scaled flow from `x ≠ -ω` never reaches the pole `-ω`. -/
theorem scaledFlow_ne_neg_pole {A : ℝ} {z ω : Eucl d} (hω : ω ∈ sphere d) (cosR : ℝ)
    (b : Block d) (hfield : b.field = scaledGatedField A z ω cosR)
    {x : Eucl d} (hx : x ≠ -ω) (t : ℝ) : b.blockFlow t x ≠ -ω := by
  intro hcontra
  have hfix : b.blockFlow t (-ω) = -ω :=
    b.blockFlow_fixed (by rw [hfield]; exact scaledGatedField_neg_pole_eq_zero hω cosR) t
  exact hx (b.blockFlow_injective t (hcontra.trans hfix.symm))

/-- The logistic coordinate stays in `(-1, 1)` along the scaled flow (poles avoided). -/
theorem inner_scaledFlow_mem_Ioo {A : ℝ} {z ω : Eucl d} (hω : ω ∈ sphere d) (cosR : ℝ)
    (b : Block d) (hfield : b.field = scaledGatedField A z ω cosR)
    {x : Eucl d} (hx : x ∈ sphere d) (hne : x ≠ ω) (hne' : x ≠ -ω) {t : ℝ} (ht : 0 ≤ t) :
    (⟪b.blockFlow t x, ω⟫ : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 :=
  inner_mem_Ioo_of_ne (b.blockFlow_mem_sphere hx ht) hω
    (scaledFlow_ne_pole hω cosR b hfield hne t) (scaledFlow_ne_neg_pole hω cosR b hfield hne' t)

/-!
## Finite-time reaching and uniform cap contraction, at amplitude `A`

These mirror `gatedBlock_reach` / `gatedBlock_mapsTo_cap` for the self-centered (`z = ω`) scaled
block; the gate constant and hence the log-odds budget scale by `A`.
-/

/-- Finite-time reaching of the self-centered scaled gated flow: budget `2·A·(⟪x,ω⟫ - cos R)·T`. -/
theorem scaledGatedBlock_reach {A : ℝ} (hA : 0 ≤ A) {ω : Eucl d} (hω : ‖ω‖ = 1) {cosR : ℝ}
    (hcosR : -1 ≤ cosR) {T : ℝ} (hT : 0 ≤ T) {x : Eucl d} (hx : x ∈ sphere d)
    (hne : x ≠ ω) (hne' : x ≠ -ω) {b : ℝ} (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (hreach : logOdds b ≤ logOdds (⟪x, ω⟫ : ℝ) + 2 * (A * ((⟪x, ω⟫ : ℝ) - cosR)) * T) :
    b ≤ (⟪(scaledGatedBlock hA hω hω hcosR hT).blockFlow T x, ω⟫ : ℝ) := by
  have hωs : ω ∈ sphere d := by rw [sphere, Metric.mem_sphere, dist_zero_right, hω]
  set B := scaledGatedBlock hA hω hω hcosR hT with hB
  have hfield : B.field = scaledGatedField A ω ω cosR := rfl
  set u : ℝ → ℝ := fun s => (⟪B.blockFlow s x, ω⟫ : ℝ) with hu_def
  set g : ℝ → ℝ := fun s => A * gateFactor ω cosR (B.blockFlow s x) with hg_def
  have hu0 : u 0 = (⟪x, ω⟫ : ℝ) := by simp [hu_def, B.blockFlow_zero]
  have hu_ode : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt u (g t * (1 - (u t) ^ 2)) t :=
    fun t ht => hasDerivAt_inner_scaledFlow hωs cosR B hfield hx ht.1
  have hu_range : ∀ t ∈ Set.Icc (0 : ℝ) T, u t ∈ Set.Ioo (-1 : ℝ) 1 :=
    fun t ht => inner_scaledFlow_mem_Ioo hωs cosR B hfield hx hne hne' ht.1
  have hg_nonneg : ∀ t, 0 ≤ g t :=
    fun t => mul_nonneg hA (gateFactor_nonneg ω cosR _)
  -- monotonicity: u' = g·(1-u²) ≥ 0
  have hmono : ∀ t ∈ Set.Icc (0 : ℝ) T, u 0 ≤ u t := by
    have hcont : ContinuousOn u (Set.Icc 0 T) :=
      fun t ht => (hu_ode t ht).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ u (interior (Set.Icc 0 T)) := by
      rw [interior_Icc]; intro t ht
      exact (hu_ode t ⟨ht.1.le, ht.2.le⟩).differentiableAt.differentiableWithinAt
    have hmono' : MonotoneOn u (Set.Icc 0 T) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 T) hcont hdiff
      intro t ht
      rw [interior_Icc] at ht
      rw [(hu_ode t ⟨ht.1.le, ht.2.le⟩).deriv]
      have h2 : (0 : ℝ) ≤ 1 - (u t) ^ 2 := by
        obtain ⟨hl, hr⟩ := hu_range t ⟨ht.1.le, ht.2.le⟩; nlinarith
      exact mul_nonneg (hg_nonneg t) h2
    exact fun t ht => hmono' (left_mem_Icc.mpr hT) ht ht.1
  -- gate lower bound: g t ≥ A·(⟪x,ω⟫ - cosR)
  have hg_lb : ∀ t ∈ Set.Icc (0 : ℝ) T, A * ((⟪x, ω⟫ : ℝ) - cosR) ≤ g t := by
    intro t ht
    have hmem : B.blockFlow t x ∈ sphere d := B.blockFlow_mem_sphere hx ht.1
    have hgt : gateFactor ω cosR (B.blockFlow t x) = reluGate ω cosR (B.blockFlow t x) :=
      gateFactor_eq_reluGate_of_mem_sphere cosR hmem
    have hcomm : (⟪ω, B.blockFlow t x⟫ : ℝ) = u t := by rw [real_inner_comm]
    have hrelu : ((⟪x, ω⟫ : ℝ) - cosR) ≤ reluGate ω cosR (B.blockFlow t x) := by
      rw [reluGate, hcomm]
      refine le_max_of_le_right ?_
      have := hmono t ht; rw [hu0] at this; linarith
    rw [hg_def]
    simp only
    rw [hgt]
    exact mul_le_mul_of_nonneg_left hrelu hA
  exact logistic_flow_reach hT hu_ode hu_range hg_lb hb (by rw [hu0]; exact hreach)

/-- Uniform cap contraction of the self-centered scaled gated flow: one uniform time `T` maps the
whole closed cap `{x ∈ 𝕊 | m ≤ ⟪x,ω⟫}` into `{y | b ≤ ⟪y,ω⟫}`, under the rim budget at
amplitude `A`. -/
theorem scaledGatedBlock_mapsTo_cap {A : ℝ} (hA : 0 ≤ A) {ω : Eucl d} (hω : ‖ω‖ = 1) {cosR : ℝ}
    (hcosR : -1 ≤ cosR) {T : ℝ} (hT : 0 ≤ T) {m b : ℝ} (hmR : cosR < m) (hm1 : m < 1)
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (hreach : logOdds b ≤ logOdds m + 2 * (A * (m - cosR)) * T) :
    Set.MapsTo ((scaledGatedBlock hA hω hω hcosR hT).blockFlow T)
      {x | x ∈ sphere d ∧ m ≤ (⟪x, ω⟫ : ℝ)} {y | b ≤ (⟪y, ω⟫ : ℝ)} := by
  have hωs : ω ∈ sphere d := by rw [sphere, Metric.mem_sphere, dist_zero_right, hω]
  intro x hx
  obtain ⟨hxs, hxm⟩ := hx
  by_cases hxω : x = ω
  · have hfix : (scaledGatedBlock hA hω hω hcosR hT).blockFlow T ω = ω :=
      (scaledGatedBlock hA hω hω hcosR hT).blockFlow_fixed
        (scaledGatedField_pole_eq_zero hωs cosR) T
    show b ≤ (⟪(scaledGatedBlock hA hω hω hcosR hT).blockFlow T x, ω⟫ : ℝ)
    rw [hxω, hfix, inner_self_eq_one_of_mem_sphere hωs]
    exact hb.2.le
  · have hxnp : x ≠ -ω := by
      intro h; subst h
      rw [inner_neg_left, inner_self_eq_one_of_mem_sphere hωs] at hxm
      linarith
    have hp_mem : (⟪x, ω⟫ : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 :=
      inner_mem_Ioo_of_ne hxs hωs hxω hxnp
    have hm_mem : m ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hm1⟩
    have hreach' : logOdds b
        ≤ logOdds (⟪x, ω⟫ : ℝ) + 2 * (A * ((⟪x, ω⟫ : ℝ) - cosR)) * T := by
      have h1 : logOdds m ≤ logOdds (⟪x, ω⟫ : ℝ) := logOdds_le_logOdds hm_mem hp_mem hxm
      have h2 : 2 * (A * (m - cosR)) * T ≤ 2 * (A * ((⟪x, ω⟫ : ℝ) - cosR)) * T := by
        have hmx : A * (m - cosR) ≤ A * ((⟪x, ω⟫ : ℝ) - cosR) :=
          mul_le_mul_of_nonneg_left (by linarith) hA
        nlinarith [mul_le_mul_of_nonneg_right hmx hT]
      linarith
    exact scaledGatedBlock_reach hA hω hcosR hT hxs hxω hxnp hb hreach'

/-- **Amplitude choice.** At any fixed horizon `T > 0`, some amplitude `A ≥ 0` meets the rim
budget, so the scaled block contracts the cap at level `m` into the cap at level `b` in time `T`.
This is the formal counterpart of the paper's parameter-norm freedom `‖θ‖ ~ C/(T·ε)`. -/
theorem exists_scaledGatedBlock_mapsTo_cap {ω : Eucl d} (hω : ‖ω‖ = 1) {cosR : ℝ}
    (hcosR : -1 ≤ cosR) {T : ℝ} (hT : 0 < T) {m b : ℝ} (hmR : cosR < m) (hm1 : m < 1)
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1) :
    ∃ (A : ℝ) (hA : 0 ≤ A),
      Set.MapsTo ((scaledGatedBlock hA hω hω hcosR hT.le).blockFlow T)
        {x | x ∈ sphere d ∧ m ≤ (⟪x, ω⟫ : ℝ)} {y | b ≤ (⟪y, ω⟫ : ℝ)} := by
  set q := (logOdds b - logOdds m) / (2 * (m - cosR) * T) with hq
  refine ⟨max 0 q, le_max_left _ _, ?_⟩
  refine scaledGatedBlock_mapsTo_cap (le_max_left 0 q) hω hcosR hT.le hmR hm1 hb ?_
  have hden : 0 < 2 * (m - cosR) * T := by
    have := sub_pos.mpr hmR; positivity
  have hqle : q ≤ max 0 q := le_max_right _ _
  have hkey : logOdds b - logOdds m ≤ 2 * (max 0 q * (m - cosR)) * T := by
    have hqmul : q * (2 * (m - cosR) * T) = logOdds b - logOdds m :=
      div_mul_cancel₀ _ hden.ne'
    calc logOdds b - logOdds m = q * (2 * (m - cosR) * T) := hqmul.symm
      _ ≤ max 0 q * (2 * (m - cosR) * T) :=
          mul_le_mul_of_nonneg_right hqle hden.le
      _ = 2 * (max 0 q * (m - cosR)) * T := by ring
  linarith

/-!
## The two-cap retention: `lemma_B_2`, proved
-/

/-- **Two-cap retention of the gated flow (Lemma B.2, proved form).** For sub-hemisphere caps
`ℬ₀ = B(z₀,R₀)`, `ℬ₁ = B(z₁,R₁)` with nonempty overlap and a probability measure `μ`, a single
gated block (one switch) transports a `(1-ε)` fraction of `μ(ℬ₀)` into `ℬ₀ ∩ ℬ₁` in any positive
time `T`. The gate is recentered at a point `ω` of the overlap; the sub-cap of `ℬ₀` carrying the
`(1-ε)` fraction (eq. B.6) lies in a cap around `ω` by the triangle inequality, and the
self-centered scaled flow contracts that cap into `B(ω, r) ⊆ ℬ₀ ∩ ℬ₁` at a sufficient amplitude.
(`_hR₁` is unused by this construction -- only `ℬ₀`'s mass is transported and `ℬ₁` enters through
the overlap point `ω` -- but is kept for signature parity with `lemma_B_2`, whose statement is
symmetric in the two caps.) -/
theorem gated_twoCap_retention (μ : Measure (Eucl d)) [IsProbabilityMeasure μ]
    (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (z₀ z₁ : Eucl d) (hz₀ : z₀ ∈ sphere d) (hz₁ : z₁ ∈ sphere d) (R₀ R₁ : ℝ)
    (hR₀ : R₀ ∈ Set.Ioo 0 (Real.pi / 2)) (_hR₁ : R₁ ∈ Set.Ioo 0 (Real.pi / 2))
    (hcap : (geodesicBall z₀ R₀ ∩ geodesicBall z₁ R₁).Nonempty) :
    ∃ θ : Params d, switches θ ≤ 1 ∧
      (1 - ENNReal.ofReal ε) * μ (geodesicBall z₀ R₀) ≤
        (Axioms.measureFlow θ T μ) (geodesicBall z₀ R₀ ∩ geodesicBall z₁ R₁) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  obtain ⟨ω, hω₀, hω₁⟩ := hcap
  have hωs : ω ∈ sphere d := hω₀.1
  have hωn : ‖ω‖ = 1 := norm_eq_one_of_mem_sphere hωs
  set a₀ := geodesicDist z₀ ω with ha₀_def
  set a₁ := geodesicDist z₁ ω with ha₁_def
  have ha₀R : a₀ < R₀ := hω₀.2
  have ha₁R : a₁ < R₁ := hω₁.2
  have ha₀0 : 0 ≤ a₀ := (geodesicDist_mem_Icc z₀ ω).1
  have ha₁0 : 0 ≤ a₁ := (geodesicDist_mem_Icc z₁ ω).1
  -- target radius: the closed cap `B(ω, r)` sits inside both balls
  set r := min (R₀ - a₀) (R₁ - a₁) / 2 with hr_def
  have hr_pos : 0 < r := by
    have h0 : 0 < R₀ - a₀ := sub_pos.mpr ha₀R
    have h1 : 0 < R₁ - a₁ := sub_pos.mpr ha₁R
    have : 0 < min (R₀ - a₀) (R₁ - a₁) := lt_min h0 h1
    positivity
  have hr_lt_pi : r < Real.pi := by
    have h0 : min (R₀ - a₀) (R₁ - a₁) ≤ R₀ - a₀ := min_le_left _ _
    have : r ≤ (R₀ - a₀) / 2 := by rw [hr_def]; linarith
    have hR₀π : R₀ < Real.pi / 2 := hR₀.2
    linarith
  have htarget : ∀ y, y ∈ sphere d → Real.cos r ≤ (⟪y, ω⟫ : ℝ) →
      y ∈ geodesicBall z₀ R₀ ∩ geodesicBall z₁ R₁ := by
    intro y hy hyr
    have hdy : geodesicDist ω y ≤ r := by
      refine geodesicDist_le_of_cos_le_inner hr_pos.le ?_
      rwa [real_inner_comm]
    have hrlt₀ : r < R₀ - a₀ := by
      have := min_le_left (R₀ - a₀) (R₁ - a₁)
      have h0 : 0 < min (R₀ - a₀) (R₁ - a₁) := lt_min (sub_pos.mpr ha₀R) (sub_pos.mpr ha₁R)
      rw [hr_def]; linarith
    have hrlt₁ : r < R₁ - a₁ := by
      have := min_le_right (R₀ - a₀) (R₁ - a₁)
      have h0 : 0 < min (R₀ - a₀) (R₁ - a₁) := lt_min (sub_pos.mpr ha₀R) (sub_pos.mpr ha₁R)
      rw [hr_def]; linarith
    refine ⟨⟨hy, ?_⟩, ⟨hy, ?_⟩⟩
    · calc geodesicDist z₀ y ≤ geodesicDist z₀ ω + geodesicDist ω y :=
            geodesicDist_triangle hz₀ hωs hy
        _ ≤ a₀ + r := add_le_add le_rfl hdy
        _ < R₀ := by linarith
    · calc geodesicDist z₁ y ≤ geodesicDist z₁ ω + geodesicDist ω y :=
            geodesicDist_triangle hz₁ hωs hy
        _ ≤ a₁ + r := add_le_add le_rfl hdy
        _ < R₁ := by linarith
  -- the (1-ε) sub-cap of `ℬ₀` (eq. B.6), over the sphere-restricted measure
  have hfcont : Continuous fun x : Eucl d => geodesicDist z₀ x := continuous_geodesicDist z₀
  have hopen : MeasurableSet {x : Eucl d | geodesicDist z₀ x < R₀} :=
    (isOpen_lt hfcont continuous_const).measurableSet
  have hfin : (μ.restrict (sphere d)) {x | geodesicDist z₀ x < R₀} ≠ ⊤ :=
    measure_ne_top _ _
  obtain ⟨r_sub, hr_sub_lt, hmass⟩ :=
    exists_closed_sublevel_mass_ge (μ := μ.restrict (sphere d)) hfcont hfin hε
  have hB₀eq : (μ.restrict (sphere d)) {x | geodesicDist z₀ x < R₀}
      = μ (geodesicBall z₀ R₀) := by
    rw [Measure.restrict_apply hopen]
    congr 1
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, geodesicBall]
    tauto
  have hSeq : (μ.restrict (sphere d)) {x | geodesicDist z₀ x ≤ r_sub}
      = μ {x | x ∈ sphere d ∧ geodesicDist z₀ x ≤ r_sub} := by
    rw [Measure.restrict_apply (measurableSet_le hfcont.measurable measurable_const)]
    congr 1
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    tauto
  -- uniform inner bound on the sub-cap: every sub-cap point is within `D'` of `ω`
  set ρ := max r_sub 0 with hρ_def
  have hρR : ρ < R₀ := max_lt hr_sub_lt hR₀.1
  set D := a₀ + ρ with hD_def
  have hD_lt : D < Real.pi := by
    have hR₀π : R₀ < Real.pi / 2 := hR₀.2
    have : D < R₀ + R₀ := by
      have := ha₀R; rw [hD_def]; linarith
    linarith
  set D' := max D (r / 2) with hD'_def
  have hD'_pos : 0 < D' := lt_of_lt_of_le (half_pos hr_pos) (le_max_right _ _)
  have hD'_lt : D' < Real.pi := by
    refine max_lt hD_lt ?_
    linarith
  set m := Real.cos D' with hm_def
  have hm_lt_one : m < 1 := by
    have := Real.strictAntiOn_cos (Set.left_mem_Icc.mpr hπ.le)
      ⟨hD'_pos.le, hD'_lt.le⟩ hD'_pos
    simpa [hm_def] using this
  have hm_gt : (-1 : ℝ) < m := by
    have := Real.strictAntiOn_cos ⟨hD'_pos.le, hD'_lt.le⟩
      (Set.right_mem_Icc.mpr hπ.le) hD'_lt
    simpa [hm_def] using this
  have hsub_source : {x | x ∈ sphere d ∧ geodesicDist z₀ x ≤ r_sub}
      ⊆ {x | x ∈ sphere d ∧ m ≤ (⟪x, ω⟫ : ℝ)} := by
    rintro x ⟨hxs, hxd⟩
    refine ⟨hxs, ?_⟩
    have hdx : geodesicDist ω x ≤ D' := by
      calc geodesicDist ω x ≤ geodesicDist ω z₀ + geodesicDist z₀ x :=
            geodesicDist_triangle hωs hz₀ hxs
        _ = a₀ + geodesicDist z₀ x := by rw [geodesicDist_comm ω z₀]
        _ ≤ a₀ + ρ := add_le_add le_rfl (hxd.trans (le_max_left _ _))
        _ ≤ D' := le_max_left _ _
    have hcos := cos_le_inner_of_geodesicDist_le hωs hxs hD'_lt.le hdx
    rw [real_inner_comm] at hcos
    exact hcos
  -- gate threshold, target level, and the amplitude
  set cosG := (m - 1) / 2 with hcosG_def
  have hcosG_ge : (-1 : ℝ) ≤ cosG := by rw [hcosG_def]; linarith
  have hcosG_lt : cosG < m := by rw [hcosG_def]; linarith
  set b := Real.cos r with hb_def
  have hb_mem : b ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · have := Real.strictAntiOn_cos ⟨hr_pos.le, hr_lt_pi.le⟩
        (Set.right_mem_Icc.mpr hπ.le) hr_lt_pi
      simpa [hb_def] using this
    · have := Real.strictAntiOn_cos (Set.left_mem_Icc.mpr hπ.le)
        ⟨hr_pos.le, hr_lt_pi.le⟩ hr_pos
      simpa [hb_def] using this
  obtain ⟨A, hA, hmaps⟩ :=
    exists_scaledGatedBlock_mapsTo_cap (d := d) hωn hcosG_ge hT hcosG_lt hm_lt_one hb_mem
  set B := scaledGatedBlock hA hωn hωn hcosG_ge hT.le with hB_def
  refine ⟨[B], ?_, ?_⟩
  · show switches [B] ≤ 1
    simp [switches]
  · -- MapsTo the sub-cap into `ℬ₀ ∩ ℬ₁`, then the pushforward bridge
    have hflow_eq : flowMap [B] T = B.blockFlow T := rfl
    have hmaps' : Set.MapsTo (flowMap [B] T)
        {x | x ∈ sphere d ∧ geodesicDist z₀ x ≤ r_sub}
        (geodesicBall z₀ R₀ ∩ geodesicBall z₁ R₁) := by
      intro x hx
      have hx' := hsub_source hx
      have h1 : b ≤ (⟪B.blockFlow T x, ω⟫ : ℝ) := hmaps hx'
      have hsphere : B.blockFlow T x ∈ sphere d := B.blockFlow_mem_sphere hx.1 hT.le
      rw [hflow_eq]
      exact htarget _ hsphere h1
    have hmeasB : MeasurableSet (geodesicBall z₀ R₀ ∩ geodesicBall z₁ R₁) :=
      (measurableSet_geodesicBall _ _).inter (measurableSet_geodesicBall _ _)
    have hbridge := Axioms.le_measureFlow_of_mapsTo [B] hT.le μ hmeasB hmaps'
    calc (1 - ENNReal.ofReal ε) * μ (geodesicBall z₀ R₀)
        = (1 - ENNReal.ofReal ε)
            * (μ.restrict (sphere d)) {x | geodesicDist z₀ x < R₀} := by rw [hB₀eq]
      _ ≤ (μ.restrict (sphere d)) {x | geodesicDist z₀ x ≤ r_sub} := hmass
      _ = μ {x | x ∈ sphere d ∧ geodesicDist z₀ x ≤ r_sub} := hSeq
      _ ≤ (Axioms.measureFlow [B] T μ) (geodesicBall z₀ R₀ ∩ geodesicBall z₁ R₁) := hbridge

end MeasureToMeasure
