import MeasureToMeasure.Foundations.GatedBlock
import MeasureToMeasure.Foundations.GeodesicDistance
import MeasureToMeasure.Foundations.LogisticReach
import MeasureToMeasure.Leaves.GateODE

/-!
# The gated flow satisfies the logistic gate ODE (Lemma B.2, discharge step 1)

This connects the concrete `gatedBlock` (`Foundations/GatedBlock.lean`) to the gate ODE leaf L2
(`Leaves/GateODE.lean`), the first step of the eventual dynamical discharge of `lemma_B_2`.

Along the block's characteristic flow `Φ_t` from a sphere point, the coordinate `u(t) = ⟪Φ_t x, ω⟫`
obeys the scalar logistic ODE

    u'(t) = gateFactor(Φ_t x) · (1 - u(t)²)     (eq. B.5),

because the gated field is exactly the tangential projection of the scaled drift `gateFactor x • ω`
(`gatedField_eq_projector_smul`), the flow stays on the sphere (`Block.blockFlow_mem_sphere`), and the
integral-curve derivative feeds directly into `gate_hasDerivAt_inner`. This statement is *sign-agnostic*
in `gateFactor`: it records that the flow obeys the logistic equation, whatever the gate's sign; the
reaching/monotonicity that the sign controls is combined later with `logistic_flow_reach`.
-/

namespace MeasureToMeasure

open scoped RealInnerProductSpace
open Set

variable {d : ℕ}

/-- **Algebraic bridge.** The gated field is the tangential projection of the scaled drift
`gateFactor x • ω`, the form the gate-ODE leaf consumes. -/
theorem gatedField_eq_projector_smul (z ω : Eucl d) (cosR : ℝ) (x : Eucl d) :
    gatedField z ω cosR x = tangentialProjector x (gateFactor z cosR x • ω) := by
  rw [gatedField, tangentialProjector_smul]

/-- On the sphere the cutoff is inactive (`‖x‖ = 1 ≤ 1`), so the gate scalar reduces to the bare ReLU
gate `(⟪z,x⟫ - cos R)₊`. -/
theorem gateFactor_eq_reluGate_of_mem_sphere {z : Eucl d} (cosR : ℝ) {x : Eucl d}
    (hx : x ∈ sphere d) : gateFactor z cosR x = reluGate z cosR x := by
  rw [gateFactor, normCutoff_eq_one (le_of_eq (norm_eq_one_of_mem_sphere hx)), one_mul]

/-- **The gate ODE for the gated flow (eq. B.5).** For any block `b` whose field is the gated field,
the coordinate `u(t) = ⟪Φ_t x, ω⟫` along the flow from a sphere point `x` obeys the logistic ODE
`u'(t) = gateFactor(Φ_t x)·(1 - u(t)²)`, for every `t ≥ 0` (`Φ_t x` stays on the sphere). -/
theorem hasDerivAt_inner_gatedFlow {z ω : Eucl d} (hω : ω ∈ sphere d) (cosR : ℝ)
    (b : Block d) (hfield : b.field = gatedField z ω cosR)
    {x : Eucl d} (hx : x ∈ sphere d) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => (⟪b.blockFlow s x, ω⟫ : ℝ))
      (gateFactor z cosR (b.blockFlow t x) * (1 - ⟪b.blockFlow t x, ω⟫ ^ 2)) t := by
  have hcurve : HasDerivAt (b.blockCurve x) (b.field (b.blockCurve x t)) t :=
    b.blockCurve_isIntegralCurve x t
  have hsph : b.blockCurve x t ∈ sphere d := b.blockFlow_mem_sphere hx ht
  have hvel : b.field (b.blockCurve x t)
      = tangentialProjector (b.blockCurve x t) (gateFactor z cosR (b.blockCurve x t) • ω) := by
    rw [hfield, gatedField_eq_projector_smul]
  exact Leaves.gate_hasDerivAt_inner hcurve hsph hω (gateFactor z cosR (b.blockCurve x t)) hvel

/-- Specialization to the canonical `gatedBlock`: its flow from a sphere point obeys the logistic gate
ODE `u'(t) = gateFactor(Φ_t x)·(1 - u(t)²)`. -/
theorem gatedBlock_hasDerivAt_inner {z ω : Eucl d} (hz : ‖z‖ = 1) (hω : ‖ω‖ = 1) {cosR : ℝ}
    (hcosR : -1 ≤ cosR) {T : ℝ} (hT : 0 ≤ T) {x : Eucl d} (hx : x ∈ sphere d) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => (⟪(gatedBlock hz hω hcosR hT).blockFlow s x, ω⟫ : ℝ))
      (gateFactor z cosR ((gatedBlock hz hω hcosR hT).blockFlow t x)
        * (1 - ⟪(gatedBlock hz hω hcosR hT).blockFlow t x, ω⟫ ^ 2)) t := by
  have hωs : ω ∈ sphere d := by rw [sphere, Metric.mem_sphere, dist_zero_right, hω]
  exact hasDerivAt_inner_gatedFlow hωs cosR (gatedBlock hz hω hcosR hT) rfl hx ht

/-!
## The flow avoids the poles `±ω`

The poles `±ω` are fixed points of the gated field (`tangentialProjector` annihilates `±ω`), so the
flow from any other point never reaches them. This keeps the logistic coordinate `u = ⟪Φ_t x, ω⟫`
strictly inside `(-1, 1)` along the whole trajectory -- the range hypothesis `logistic_flow_reach`
needs, now supplied for every `t ≥ 0` rather than assumed.
-/

/-- `ω` is a fixed point of the gated field: the tangential projector annihilates `ω`. -/
theorem gatedField_pole_eq_zero {z ω : Eucl d} (hω : ω ∈ sphere d) (cosR : ℝ) :
    gatedField z ω cosR ω = 0 := by
  rw [gatedField, tangentialProjector_self hω, smul_zero]

/-- `-ω` is a fixed point of the gated field: `P_{-ω}^⊥ ω = ω - ⟪-ω,ω⟫(-ω) = ω - ω = 0`. -/
theorem gatedField_neg_pole_eq_zero {z ω : Eucl d} (hω : ω ∈ sphere d) (cosR : ℝ) :
    gatedField z ω cosR (-ω) = 0 := by
  have hproj : tangentialProjector (-ω) ω = 0 := by
    rw [tangentialProjector, inner_neg_left, inner_self_eq_one_of_mem_sphere hω]; module
  rw [gatedField, hproj, smul_zero]

/-- The flow from `x ≠ ω` never reaches the pole `ω` (uniqueness: `ω` is fixed, and `blockFlow t` is
injective). -/
theorem blockFlow_ne_pole {z ω : Eucl d} (hω : ω ∈ sphere d) (cosR : ℝ)
    (b : Block d) (hfield : b.field = gatedField z ω cosR)
    {x : Eucl d} (hx : x ≠ ω) (t : ℝ) : b.blockFlow t x ≠ ω := by
  intro hcontra
  have hfix : b.blockFlow t ω = ω :=
    b.blockFlow_fixed (by rw [hfield]; exact gatedField_pole_eq_zero hω cosR) t
  exact hx (b.blockFlow_injective t (hcontra.trans hfix.symm))

/-- The flow from `x ≠ -ω` never reaches the pole `-ω`. -/
theorem blockFlow_ne_neg_pole {z ω : Eucl d} (hω : ω ∈ sphere d) (cosR : ℝ)
    (b : Block d) (hfield : b.field = gatedField z ω cosR)
    {x : Eucl d} (hx : x ≠ -ω) (t : ℝ) : b.blockFlow t x ≠ -ω := by
  intro hcontra
  have hfix : b.blockFlow t (-ω) = -ω :=
    b.blockFlow_fixed (by rw [hfield]; exact gatedField_neg_pole_eq_zero hω cosR) t
  exact hx (b.blockFlow_injective t (hcontra.trans hfix.symm))

/-- **The logistic coordinate stays in `(-1, 1)` along the flow.** For `x` on the sphere with
`x ≠ ±ω`, the flow avoids the poles, so `u(t) = ⟪Φ_t x, ω⟫ ∈ (-1, 1)` for every `t ≥ 0` -- exactly the
range hypothesis `logistic_flow_reach` requires along the trajectory. -/
theorem inner_gatedFlow_mem_Ioo {z ω : Eucl d} (hω : ω ∈ sphere d) (cosR : ℝ)
    (b : Block d) (hfield : b.field = gatedField z ω cosR)
    {x : Eucl d} (hx : x ∈ sphere d) (hne : x ≠ ω) (hne' : x ≠ -ω) {t : ℝ} (ht : 0 ≤ t) :
    (⟪b.blockFlow t x, ω⟫ : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 :=
  inner_mem_Ioo_of_ne (b.blockFlow_mem_sphere hx ht) hω
    (blockFlow_ne_pole hω cosR b hfield hne t) (blockFlow_ne_neg_pole hω cosR b hfield hne' t)

/-!
## Finite-time reaching for the self-centered gated flow (Lemma B.2, discharge step 3)

For the block centered at its own drift target (`z = ω`), the gated flow *contracts a cap toward
`ω`*: this is the essential dynamical content of B.7. The coordinate `u(t) = ⟪Φ_t x, ω⟫` is monotone
non-decreasing (`u' = g(1-u²) ≥ 0`, since the gate is nonnegative and `u ∈ (-1,1)`), so it never falls
below its start `u(0) > cos R`; hence the gate `g(t) = (u(t) - cos R)₊ ≥ u(0) - cos R =: c₀ > 0` stays
uniformly positive, with *no circularity*. Feeding this into `logistic_flow_reach` gives: from any
point strictly inside the cap `B(ω, R)`, the flow reaches any target level `b < 1` once `T` is large
enough — i.e. drives `x` into the sub-cap `B(ω, arccos b)`.
-/

/-- The gate scalar is nonnegative (cutoff and ReLU gate are each nonnegative). -/
theorem gateFactor_nonneg (z : Eucl d) (cosR : ℝ) (x : Eucl d) : 0 ≤ gateFactor z cosR x :=
  mul_nonneg (normCutoff_nonneg x) (reluGate_nonneg z cosR x)

/-- **Finite-time reaching of the self-centered gated flow (eq. B.7).** For `z = ω`, from a sphere
point `x` (`x ≠ ±ω`), the gated flow drives the coordinate `⟪Φ_T x, ω⟫` to any target level `b < 1`,
provided `T` is large enough that the log-odds budget `logOdds b ≤ logOdds ⟪x,ω⟫ + 2·(⟪x,ω⟫ - cos R)·T`
is met. Equivalently, `Φ_T x` lands in the sub-cap `{ y | b ≤ ⟪y, ω⟫ }` of `ω`. The estimate is
nontrivial precisely in the active region `cos R < ⟪x, ω⟫` (`x` strictly inside `B(ω, R)`), where the
gate constant `c₀ = ⟪x,ω⟫ - cos R` is positive and the budget is satisfiable for `b` up to `1`. -/
theorem gatedBlock_reach {ω : Eucl d} (hω : ‖ω‖ = 1) {cosR : ℝ} (hcosR : -1 ≤ cosR)
    {T : ℝ} (hT : 0 ≤ T) {x : Eucl d} (hx : x ∈ sphere d) (hne : x ≠ ω) (hne' : x ≠ -ω)
    {b : ℝ} (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (hreach : logOdds b ≤ logOdds (⟪x, ω⟫ : ℝ) + 2 * ((⟪x, ω⟫ : ℝ) - cosR) * T) :
    b ≤ (⟪(gatedBlock hω hω hcosR hT).blockFlow T x, ω⟫ : ℝ) := by
  have hωs : ω ∈ sphere d := by rw [sphere, Metric.mem_sphere, dist_zero_right, hω]
  set B := gatedBlock hω hω hcosR hT with hB
  set u : ℝ → ℝ := fun s => (⟪B.blockFlow s x, ω⟫ : ℝ) with hu_def
  set g : ℝ → ℝ := fun s => gateFactor ω cosR (B.blockFlow s x) with hg_def
  have hu0 : u 0 = (⟪x, ω⟫ : ℝ) := by simp [hu_def, B.blockFlow_zero]
  -- the gate ODE and the range, along the flow
  have hu_ode : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt u (g t * (1 - (u t) ^ 2)) t :=
    fun t ht => gatedBlock_hasDerivAt_inner hω hω hcosR hT hx ht.1
  have hu_range : ∀ t ∈ Set.Icc (0 : ℝ) T, u t ∈ Set.Ioo (-1 : ℝ) 1 :=
    fun t ht => inner_gatedFlow_mem_Ioo hωs cosR B rfl hx hne hne' ht.1
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
      exact mul_nonneg (gateFactor_nonneg ω cosR _) h2
    exact fun t ht => hmono' (left_mem_Icc.mpr hT) ht ht.1
  -- gate lower bound: g t ≥ c₀ = ⟪x,ω⟫ - cosR, since u t ≥ u 0 > cosR (self-centered)
  have hg_lb : ∀ t ∈ Set.Icc (0 : ℝ) T, ((⟪x, ω⟫ : ℝ) - cosR) ≤ g t := by
    intro t ht
    have hmem : B.blockFlow t x ∈ sphere d := B.blockFlow_mem_sphere hx ht.1
    have hgt : g t = reluGate ω cosR (B.blockFlow t x) :=
      gateFactor_eq_reluGate_of_mem_sphere cosR hmem
    have hcomm : (⟪ω, B.blockFlow t x⟫ : ℝ) = u t := by rw [real_inner_comm]
    rw [hgt, reluGate, hcomm]
    refine le_max_of_le_right ?_
    have := hmono t ht; rw [hu0] at this; linarith
  -- assemble via the logistic reaching estimate
  have hfin := logistic_flow_reach hT hu_ode hu_range hg_lb hb (by rw [hu0]; exact hreach)
  exact hfin

/-!
## Uniform cap contraction (Lemma B.2, discharge step 4: the set-level reaching statement)

`gatedBlock_reach` is *pointwise*: its budget `logOdds b ≤ logOdds ⟪x,ω⟫ + 2·(⟪x,ω⟫ - cos R)·T` depends
on the starting point `x`. To feed the mass-retention bridge `Axioms.le_measureFlow_of_mapsTo` we need a
`Set.MapsTo`: *every* point of a cap flows into a smaller cap under one uniform duration `T`.

The self-centered flow makes this uniform for free. Because `u = ⟪·,ω⟫` is monotone non-decreasing
along the flow, both point-dependent terms in the budget are worst at the cap's inner rim `u = m`: the
gate constant `⟪x,ω⟫ - cos R ≥ m - cos R`, and `logOdds ⟪x,ω⟫ ≥ logOdds m` (monotonicity, `logOdds_le_logOdds`).
So a single budget `logOdds b ≤ logOdds m + 2·(m - cos R)·T` at the rim implies the pointwise budget
everywhere on the closed sub-cap `{ x ∈ 𝕊 | m ≤ ⟪x,ω⟫ }`. In the sphere's geodesic terms this is the cap
`B(ω, arccos m) ⊆ B(ω, R)` (since `⟪x,ω⟫ ≥ c ⟺ geodesicDist ω x ≤ arccos c`); the flow drives it into the
smaller cap `{ y | b ≤ ⟪y,ω⟫ } = B(ω, arccos b)`.
-/

/-- **Uniform cap contraction of the self-centered gated flow (eq. B.7, set form).** For `z = ω`, the
flow at a single uniform time `T` maps the whole closed sub-cap `{ x ∈ 𝕊 | m ≤ ⟪x,ω⟫ }` (with `m` strictly
inside the active region, `cos R < m < 1`) into the target cap `{ y | b ≤ ⟪y,ω⟫ }`, provided the rim
budget `logOdds b ≤ logOdds m + 2·(m - cos R)·T` holds. This is the point-to-set upgrade of
`gatedBlock_reach`, obtained by minimizing the pointwise budget over the cap (monotonicity of both the
gate constant and `logOdds`). It plugs directly into `Axioms.le_measureFlow_of_mapsTo` to yield a mass
statement: `μ {x ∈ 𝕊 | m ≤ ⟪x,ω⟫} ≤ measureFlow θ T μ {y | b ≤ ⟪y,ω⟫}`. The pole `x = ω` lies in the
source cap and is handled separately (it is a fixed point, and `⟪ω,ω⟫ = 1 ≥ b`). -/
theorem gatedBlock_mapsTo_cap {ω : Eucl d} (hω : ‖ω‖ = 1) {cosR : ℝ} (hcosR : -1 ≤ cosR)
    {T : ℝ} (hT : 0 ≤ T) {m b : ℝ} (hmR : cosR < m) (hm1 : m < 1)
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (hreach : logOdds b ≤ logOdds m + 2 * (m - cosR) * T) :
    Set.MapsTo ((gatedBlock hω hω hcosR hT).blockFlow T)
      {x | x ∈ sphere d ∧ m ≤ (⟪x, ω⟫ : ℝ)} {y | b ≤ (⟪y, ω⟫ : ℝ)} := by
  have hωs : ω ∈ sphere d := by rw [sphere, Metric.mem_sphere, dist_zero_right, hω]
  intro x hx
  obtain ⟨hxs, hxm⟩ := hx
  by_cases hxω : x = ω
  · -- the centre is a fixed point of the flow, and `⟪ω,ω⟫ = 1 ≥ b`
    have hfix : (gatedBlock hω hω hcosR hT).blockFlow T ω = ω :=
      (gatedBlock hω hω hcosR hT).blockFlow_fixed (gatedField_pole_eq_zero hωs cosR) T
    show b ≤ (⟪(gatedBlock hω hω hcosR hT).blockFlow T x, ω⟫ : ℝ)
    rw [hxω, hfix, inner_self_eq_one_of_mem_sphere hωs]
    exact hb.2.le
  · -- off the centre: minimise the pointwise budget over the cap, then apply `gatedBlock_reach`
    have hxnp : x ≠ -ω := by
      intro h; subst h
      rw [inner_neg_left, inner_self_eq_one_of_mem_sphere hωs] at hxm
      linarith
    have hp_mem : (⟪x, ω⟫ : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 :=
      inner_mem_Ioo_of_ne hxs hωs hxω hxnp
    have hm_mem : m ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hm1⟩
    have hreach' : logOdds b ≤ logOdds (⟪x, ω⟫ : ℝ) + 2 * ((⟪x, ω⟫ : ℝ) - cosR) * T := by
      have h1 : logOdds m ≤ logOdds (⟪x, ω⟫ : ℝ) := logOdds_le_logOdds hm_mem hp_mem hxm
      have h2 : 2 * (m - cosR) * T ≤ 2 * ((⟪x, ω⟫ : ℝ) - cosR) * T := by
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (⟪x, ω⟫ : ℝ) - m) hT]
      linarith
    exact gatedBlock_reach hω hcosR hT hxs hxω hxnp hb hreach'

end MeasureToMeasure
