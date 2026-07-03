import MeasureToMeasure.Foundations.GatedBlock
import MeasureToMeasure.Foundations.GeodesicDistance
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

end MeasureToMeasure
