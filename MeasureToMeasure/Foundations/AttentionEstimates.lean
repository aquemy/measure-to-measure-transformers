import MeasureToMeasure.Foundations.Attention
import MeasureToMeasure.Foundations.Wasserstein
import MeasureToMeasure.Foundations.GatedBlock

/-!
# Quantitative estimates for the self-attention field (M3b groundwork)

Discharging the mean-field well-posedness axioms (`exists_meanFieldFlow`,
`meanFieldFlow_unique`) is a Picard-Lindelöf iteration in the pair (point, measure): the field
must be Lipschitz in the point and Lipschitz in the measure for a transport metric. This file
lays the *first half* of that groundwork, kernel-clean, for sphere-supported probability
measures — the point modulus and the measure-side dual-pairing tool:

* kernel bounds: on the sphere the Gibbs kernel `e^{⟪Bx, z⟫}` lives in
  `[e^{-‖B‖}, e^{‖B‖}]`, so the softmax denominator is uniformly positive
  (`denom_ge_exp_neg`, `denom_le_exp`) and the average is bounded (`norm_attnAvg_le`);
* the point modulus: `attnAvg_sub_le_of_norm_le` gives
  `‖A_B[μ](x) - A_B[μ](y)‖ ≤ 2 ‖B‖ e^{4‖B‖} ‖x - y‖`;
* a vector-valued Kantorovich-Rubinstein bound (`ofReal_norm_integral_sub_le_W1`): for a
  `c`-Lipschitz vector integrand, `‖∫ g dμ - ∫ g dν‖ ≤ c · W₁(μ, ν)` -- the measure-side tool
  (the scalar form `ofReal_integral_sub_le_W1` is the existing KR machinery);
* the `W₁` diameter bound (`W1_le_of_ae_norm_le`, `W1_ne_top_of_sphere_supported`): probability
  measures a.e.-supported in the radius-`R` ball are within `W₁ ≤ 2R`, so sphere-supported pairs
  have `W₁ ≤ 2 < ⊤` and the iteration works in a genuine (pseudo)metric.

## Remaining for M3b (NOT in this file)

The point modulus and the vector KR tool are the reusable, kernel-clean core. The following
ingredients — planned but **not yet formalized** — complete the Picard argument and are tracked
in `RESEARCH.md` (M3b plan). They are named here as future work, not as results of this file:

* the **measure modulus** `‖A_B[μ](x) - A_B[ν](x)‖ ≤ K_B · (W₁ μ ν).toReal`. The obstruction is
  that `z ↦ e^{⟪Bx,z⟫} z` is not globally Lipschitz, so the KR tool above needs globally-Lipschitz
  surrogates that agree with the kernel on the sphere (a clamped exponential, and the
  `normCutoff z • z` capping from `Foundations/GatedBlock.lean`);
* the **field modulus**: the field inherits both point and measure moduli through the value matrix
  and the tangential projector;
* **transport-metric comparisons** on the sphere (`W₁ ≤ W₂ ≤ √(2 W₁)`), so the iteration may
  contract in `W₁` and conclude in `W₂`;
* **completeness/compactness** of the sphere-supported probability measures under `W₂`. Mathlib
  `v4.31.0` supplies Prokhorov (`MeasureTheory.Measure.Prokhorov`) and the Lévy-Prokhorov
  metrization; what is missing is the bridge "`W₂` topology = weak topology on a compact base"
  (comparisons between `W₂` and the Lévy-Prokhorov distance).
-/

namespace MeasureToMeasure.Foundations

open MeasureTheory MeasureToMeasure
open scoped RealInnerProductSpace ENNReal NNReal

variable {d : ℕ}

/-! ### Scalar helpers -/

/-- Mean-value bound for the exponential on a half-line: if both exponents are at most `M`,
`|e^a - e^b| ≤ e^M |a - b|`. -/
theorem abs_exp_sub_exp_le {a b M : ℝ} (ha : a ≤ M) (hb : b ≤ M) :
    |Real.exp a - Real.exp b| ≤ Real.exp M * |a - b| := by
  wlog hab : b ≤ a generalizing a b
  · have := this hb ha (le_of_not_ge hab)
    rwa [abs_sub_comm, abs_sub_comm b a] at this
  -- `e^a - e^b = e^b (e^{a-b} - 1) ≤ e^b (a-b) e^{a-b} = (a-b) e^a ≤ (a-b) e^M`.
  have h1 : Real.exp a - Real.exp b ≤ (a - b) * Real.exp a := by
    have hexp : b - a + 1 ≤ Real.exp (b - a) := Real.add_one_le_exp (b - a)
    have := mul_le_mul_of_nonneg_right hexp (Real.exp_pos a).le
    rw [← Real.exp_add] at this
    have hba : b - a + a = b := by ring
    rw [hba] at this
    nlinarith [Real.exp_pos a]
  have h2 : 0 ≤ Real.exp a - Real.exp b := by
    have := Real.exp_le_exp.mpr hab
    linarith
  rw [abs_of_nonneg h2, abs_of_nonneg (by linarith : (0:ℝ) ≤ a - b)]
  calc Real.exp a - Real.exp b ≤ (a - b) * Real.exp a := h1
    _ ≤ (a - b) * Real.exp M := by
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ha) (by linarith)
    _ = Real.exp M * (a - b) := by ring

/-- On the sphere, the attention exponent is bounded by the operator norm: for `‖x‖ ≤ 1` and
`z ∈ sphere d`, `|⟪B x, z⟫| ≤ ‖B‖`. -/
theorem abs_inner_attn_le (B : Eucl d →L[ℝ] Eucl d) {x z : Eucl d} (hx : ‖x‖ ≤ 1)
    (hz : z ∈ sphere d) : |⟪B x, z⟫| ≤ ‖B‖ := by
  have hzn : ‖z‖ = 1 := norm_eq_one_of_mem_sphere hz
  calc |⟪B x, z⟫| ≤ ‖B x‖ * ‖z‖ := abs_real_inner_le_norm _ _
    _ = ‖B x‖ := by rw [hzn, mul_one]
    _ ≤ ‖B‖ * ‖x‖ := B.le_opNorm x
    _ ≤ ‖B‖ * 1 := by
        exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)
    _ = ‖B‖ := mul_one _

/-! ### Kernel bounds and integrability

Throughout, `μ` is a sphere-supported probability measure and `‖x‖ ≤ 1`; the a.e. versions of the
pointwise bounds transfer through `measure_mono_null` from the support hypothesis
`μ (sphere d)ᶜ = 0`. -/

section KernelBounds

variable (B : Eucl d →L[ℝ] Eucl d) {μ : Measure (Eucl d)} {x : Eucl d}

/-- Sphere support upgrades a pointwise-on-sphere statement to an a.e. statement. -/
theorem ae_of_sphere_supported (hs : μ (sphere d)ᶜ = 0) {P : Eucl d → Prop}
    (hP : ∀ z ∈ sphere d, P z) : ∀ᵐ z ∂μ, P z := by
  rw [ae_iff]
  refine measure_mono_null (fun z hz => ?_) hs
  simp only [Set.mem_setOf_eq] at hz
  simp only [Set.mem_compl_iff]
  exact fun hzs => hz (hP z hzs)

/-- The attention kernel is continuous in `z`. -/
theorem continuous_attnKernel : Continuous fun z : Eucl d => Real.exp ⟪B x, z⟫ :=
  Real.continuous_exp.comp (continuous_const.inner continuous_id)

/-- The attention kernel is integrable against a sphere-supported finite measure. -/
theorem integrable_attnKernel [IsFiniteMeasure μ] (hs : μ (sphere d)ᶜ = 0) (hx : ‖x‖ ≤ 1) :
    Integrable (fun z => Real.exp ⟪B x, z⟫) μ := by
  refine Integrable.mono' (integrable_const (Real.exp ‖B‖))
    (continuous_attnKernel B).aestronglyMeasurable ?_
  refine ae_of_sphere_supported hs fun z hz => ?_
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans (abs_inner_attn_le B hx hz))

/-- The vector attention integrand `z ↦ e^{⟪Bx,z⟫} z` is integrable against a sphere-supported
finite measure. -/
theorem integrable_attnKernel_smul [IsFiniteMeasure μ] (hs : μ (sphere d)ᶜ = 0)
    (hx : ‖x‖ ≤ 1) : Integrable (fun z => Real.exp ⟪B x, z⟫ • z) μ := by
  refine Integrable.mono' (integrable_const (Real.exp ‖B‖))
    (((continuous_attnKernel B).smul continuous_id).aestronglyMeasurable) ?_
  refine ae_of_sphere_supported hs fun z hz => ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    norm_eq_one_of_mem_sphere hz, mul_one]
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans (abs_inner_attn_le B hx hz))

/-- The softmax denominator of a sphere-supported probability measure is at least `e^{-‖B‖}`. -/
theorem denom_ge_exp_neg [IsProbabilityMeasure μ] (hs : μ (sphere d)ᶜ = 0) (hx : ‖x‖ ≤ 1) :
    Real.exp (-‖B‖) ≤ ∫ z, Real.exp ⟪B x, z⟫ ∂μ := by
  have hlow : ∀ᵐ z ∂μ, Real.exp (-‖B‖) ≤ Real.exp ⟪B x, z⟫ :=
    ae_of_sphere_supported hs fun z hz =>
      Real.exp_le_exp.mpr (neg_le_of_abs_le (abs_inner_attn_le B hx hz))
  calc Real.exp (-‖B‖) = ∫ _, Real.exp (-‖B‖) ∂μ := by simp
    _ ≤ ∫ z, Real.exp ⟪B x, z⟫ ∂μ :=
        integral_mono_ae (integrable_const _) (integrable_attnKernel B hs hx) hlow

/-- The softmax denominator of a sphere-supported probability measure is at most `e^{‖B‖}`. -/
theorem denom_le_exp [IsProbabilityMeasure μ] (hs : μ (sphere d)ᶜ = 0) (hx : ‖x‖ ≤ 1) :
    ∫ z, Real.exp ⟪B x, z⟫ ∂μ ≤ Real.exp ‖B‖ := by
  have hup : ∀ᵐ z ∂μ, Real.exp ⟪B x, z⟫ ≤ Real.exp ‖B‖ :=
    ae_of_sphere_supported hs fun z hz =>
      Real.exp_le_exp.mpr ((le_abs_self _).trans (abs_inner_attn_le B hx hz))
  calc ∫ z, Real.exp ⟪B x, z⟫ ∂μ ≤ ∫ _, Real.exp ‖B‖ ∂μ :=
        integral_mono_ae (integrable_attnKernel B hs hx) (integrable_const _) hup
    _ = Real.exp ‖B‖ := by simp

/-- The vector numerator is bounded by `e^{‖B‖}` in norm. -/
theorem norm_num_integral_le [IsProbabilityMeasure μ] (hs : μ (sphere d)ᶜ = 0)
    (hx : ‖x‖ ≤ 1) : ‖∫ z, Real.exp ⟪B x, z⟫ • z ∂μ‖ ≤ Real.exp ‖B‖ := by
  have hbd : ∀ᵐ z ∂μ, ‖Real.exp ⟪B x, z⟫ • z‖ ≤ Real.exp ‖B‖ := by
    refine ae_of_sphere_supported hs fun z hz => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      norm_eq_one_of_mem_sphere hz, mul_one]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (abs_inner_attn_le B hx hz))
  calc ‖∫ z, Real.exp ⟪B x, z⟫ • z ∂μ‖ ≤ ∫ z, ‖Real.exp ⟪B x, z⟫ • z‖ ∂μ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ _, Real.exp ‖B‖ ∂μ :=
        integral_mono_ae (integrable_attnKernel_smul B hs hx).norm (integrable_const _)
          hbd
    _ = Real.exp ‖B‖ := by simp

/-- The softmax average of a sphere-supported probability measure is bounded:
`‖A_B[μ](x)‖ ≤ e^{2‖B‖}`. -/
theorem norm_attnAvg_le [IsProbabilityMeasure μ] (hs : μ (sphere d)ᶜ = 0) (hx : ‖x‖ ≤ 1) :
    ‖attnAvg B μ x‖ ≤ Real.exp (2 * ‖B‖) := by
  rw [attnAvg, norm_smul, Real.norm_eq_abs]
  have hN := denom_ge_exp_neg B hs hx
  have hNpos : (0:ℝ) < ∫ z, Real.exp ⟪B x, z⟫ ∂μ := lt_of_lt_of_le (Real.exp_pos _) hN
  have hinv : |(∫ z, Real.exp ⟪B x, z⟫ ∂μ)⁻¹| ≤ Real.exp ‖B‖ := by
    rw [abs_of_pos (inv_pos.mpr hNpos)]
    rw [inv_le_comm₀ hNpos (Real.exp_pos _)]
    calc (Real.exp ‖B‖)⁻¹ = Real.exp (-‖B‖) := (Real.exp_neg _).symm
      _ ≤ ∫ z, Real.exp ⟪B x, z⟫ ∂μ := hN
  calc |(∫ z, Real.exp ⟪B x, z⟫ ∂μ)⁻¹| * ‖∫ z, Real.exp ⟪B x, z⟫ • z ∂μ‖
      ≤ Real.exp ‖B‖ * Real.exp ‖B‖ :=
        mul_le_mul hinv (norm_num_integral_le B hs hx) (norm_nonneg _)
          (Real.exp_pos _).le
    _ = Real.exp (2 * ‖B‖) := by rw [← Real.exp_add]; ring_nf

end KernelBounds

/-! ### The point modulus: `x ↦ A_B[μ](x)` is Lipschitz on the unit ball -/

section PointModulus

variable (B : Eucl d →L[ℝ] Eucl d) {μ : Measure (Eucl d)} {x y : Eucl d}

/-- Pointwise kernel increment: for `‖x‖, ‖y‖ ≤ 1` and `z` on the sphere,
`|e^{⟪Bx,z⟫} - e^{⟪By,z⟫}| ≤ e^{‖B‖} ‖B‖ ‖x - y‖`. -/
theorem abs_kernel_sub_le (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) {z : Eucl d} (hz : z ∈ sphere d) :
    |Real.exp ⟪B x, z⟫ - Real.exp ⟪B y, z⟫| ≤ Real.exp ‖B‖ * (‖B‖ * ‖x - y‖) := by
  have ha : ⟪B x, z⟫ ≤ ‖B‖ := (le_abs_self _).trans (abs_inner_attn_le B hx hz)
  have hb : ⟪B y, z⟫ ≤ ‖B‖ := (le_abs_self _).trans (abs_inner_attn_le B hy hz)
  have hzn : ‖z‖ = 1 := norm_eq_one_of_mem_sphere hz
  have hdiff : |⟪B x, z⟫ - ⟪B y, z⟫| ≤ ‖B‖ * ‖x - y‖ := by
    have : ⟪B x, z⟫ - ⟪B y, z⟫ = ⟪B (x - y), z⟫ := by
      rw [map_sub]; exact (inner_sub_left _ _ _).symm
    rw [this]
    calc |⟪B (x - y), z⟫| ≤ ‖B (x - y)‖ * ‖z‖ := abs_real_inner_le_norm _ _
      _ = ‖B (x - y)‖ := by rw [hzn, mul_one]
      _ ≤ ‖B‖ * ‖x - y‖ := B.le_opNorm _
  calc |Real.exp ⟪B x, z⟫ - Real.exp ⟪B y, z⟫|
      ≤ Real.exp ‖B‖ * |⟪B x, z⟫ - ⟪B y, z⟫| := abs_exp_sub_exp_le ha hb
    _ ≤ Real.exp ‖B‖ * (‖B‖ * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left hdiff (Real.exp_pos _).le

/-- Denominator increment in the point variable. -/
theorem denom_sub_le [IsProbabilityMeasure μ] (hs : μ (sphere d)ᶜ = 0)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |(∫ z, Real.exp ⟪B x, z⟫ ∂μ) - ∫ z, Real.exp ⟪B y, z⟫ ∂μ| ≤
      Real.exp ‖B‖ * (‖B‖ * ‖x - y‖) := by
  rw [← integral_sub (integrable_attnKernel B hs hx) (integrable_attnKernel B hs hy)]
  calc |∫ z, (Real.exp ⟪B x, z⟫ - Real.exp ⟪B y, z⟫) ∂μ|
      ≤ ∫ z, |Real.exp ⟪B x, z⟫ - Real.exp ⟪B y, z⟫| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _, Real.exp ‖B‖ * (‖B‖ * ‖x - y‖) ∂μ := by
        refine integral_mono_ae
          ((integrable_attnKernel B hs hx).sub (integrable_attnKernel B hs hy)).abs
          (integrable_const _) ?_
        exact ae_of_sphere_supported hs fun z hz => abs_kernel_sub_le B hx hy hz
    _ = Real.exp ‖B‖ * (‖B‖ * ‖x - y‖) := by simp

/-- Numerator increment in the point variable. -/
theorem num_sub_le [IsProbabilityMeasure μ] (hs : μ (sphere d)ᶜ = 0)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖(∫ z, Real.exp ⟪B x, z⟫ • z ∂μ) - ∫ z, Real.exp ⟪B y, z⟫ • z ∂μ‖ ≤
      Real.exp ‖B‖ * (‖B‖ * ‖x - y‖) := by
  rw [← integral_sub (integrable_attnKernel_smul B hs hx) (integrable_attnKernel_smul B hs hy)]
  calc ‖∫ z, (Real.exp ⟪B x, z⟫ • z - Real.exp ⟪B y, z⟫ • z) ∂μ‖
      ≤ ∫ z, ‖Real.exp ⟪B x, z⟫ • z - Real.exp ⟪B y, z⟫ • z‖ ∂μ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ _, Real.exp ‖B‖ * (‖B‖ * ‖x - y‖) ∂μ := by
        refine integral_mono_ae
          ((integrable_attnKernel_smul B hs hx).sub
            (integrable_attnKernel_smul B hs hy)).norm (integrable_const _) ?_
        refine ae_of_sphere_supported hs fun z hz => ?_
        simp only [← sub_smul, norm_smul, Real.norm_eq_abs,
          norm_eq_one_of_mem_sphere hz, mul_one]
        exact abs_kernel_sub_le B hx hy hz
    _ = Real.exp ‖B‖ * (‖B‖ * ‖x - y‖) := by simp

/-- **The point modulus.** For a sphere-supported probability measure and points of the unit
ball, the softmax average is Lipschitz: `‖A_B[μ](x) - A_B[μ](y)‖ ≤ 2 ‖B‖ e^{4‖B‖} ‖x - y‖`. -/
theorem attnAvg_sub_le_of_norm_le [IsProbabilityMeasure μ] (hs : μ (sphere d)ᶜ = 0)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖attnAvg B μ x - attnAvg B μ y‖ ≤ 2 * ‖B‖ * Real.exp (4 * ‖B‖) * ‖x - y‖ := by
  set Nx := ∫ z, Real.exp ⟪B x, z⟫ ∂μ with hNx
  set Ny := ∫ z, Real.exp ⟪B y, z⟫ ∂μ with hNy
  set Ix := ∫ z, Real.exp ⟪B x, z⟫ • z ∂μ with hIx
  set Iy := ∫ z, Real.exp ⟪B y, z⟫ • z ∂μ with hIy
  have hNxpos : (0:ℝ) < Nx := lt_of_lt_of_le (Real.exp_pos _) (denom_ge_exp_neg B hs hx)
  have hNypos : (0:ℝ) < Ny := lt_of_lt_of_le (Real.exp_pos _) (denom_ge_exp_neg B hs hy)
  have hNxinv : Nx⁻¹ ≤ Real.exp ‖B‖ := by
    rw [inv_le_comm₀ hNxpos (Real.exp_pos _)]
    calc (Real.exp ‖B‖)⁻¹ = Real.exp (-‖B‖) := (Real.exp_neg _).symm
      _ ≤ Nx := denom_ge_exp_neg B hs hx
  have hNyinv : Ny⁻¹ ≤ Real.exp ‖B‖ := by
    rw [inv_le_comm₀ hNypos (Real.exp_pos _)]
    calc (Real.exp ‖B‖)⁻¹ = Real.exp (-‖B‖) := (Real.exp_neg _).symm
      _ ≤ Ny := denom_ge_exp_neg B hs hy
  have hIynorm : ‖Iy‖ ≤ Real.exp ‖B‖ := norm_num_integral_le B hs hy
  -- Split through the mid-point `Nx⁻¹ • Iy`.
  have hsplit : attnAvg B μ x - attnAvg B μ y
      = Nx⁻¹ • (Ix - Iy) + (Nx⁻¹ - Ny⁻¹) • Iy := by
    rw [attnAvg, attnAvg, ← hNx, ← hNy, ← hIx, ← hIy]
    rw [smul_sub, sub_smul]
    abel
  rw [hsplit]
  have hterm1 : ‖Nx⁻¹ • (Ix - Iy)‖ ≤ Real.exp ‖B‖ * (Real.exp ‖B‖ * (‖B‖ * ‖x - y‖)) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hNxpos)]
    exact mul_le_mul hNxinv (num_sub_le B hs hx hy) (norm_nonneg _) (Real.exp_pos _).le
  have hterm2 : ‖(Nx⁻¹ - Ny⁻¹) • Iy‖ ≤
      Real.exp ‖B‖ * Real.exp ‖B‖ * (Real.exp ‖B‖ * (‖B‖ * ‖x - y‖)) * Real.exp ‖B‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    have hinvdiff : |Nx⁻¹ - Ny⁻¹| ≤
        Real.exp ‖B‖ * Real.exp ‖B‖ * (Real.exp ‖B‖ * (‖B‖ * ‖x - y‖)) := by
      have hrw : Nx⁻¹ - Ny⁻¹ = (Ny - Nx) * (Nx⁻¹ * Ny⁻¹) := by
        field_simp
      rw [hrw, abs_mul]
      have h1 : |Ny - Nx| ≤ Real.exp ‖B‖ * (‖B‖ * ‖x - y‖) := by
        rw [abs_sub_comm]; exact denom_sub_le B hs hx hy
      have h2 : |Nx⁻¹ * Ny⁻¹| ≤ Real.exp ‖B‖ * Real.exp ‖B‖ := by
        rw [abs_mul, abs_of_pos (inv_pos.mpr hNxpos), abs_of_pos (inv_pos.mpr hNypos)]
        exact mul_le_mul hNxinv hNyinv (inv_pos.mpr hNypos).le (Real.exp_pos _).le
      calc |Ny - Nx| * |Nx⁻¹ * Ny⁻¹|
          ≤ (Real.exp ‖B‖ * (‖B‖ * ‖x - y‖)) * (Real.exp ‖B‖ * Real.exp ‖B‖) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = Real.exp ‖B‖ * Real.exp ‖B‖ * (Real.exp ‖B‖ * (‖B‖ * ‖x - y‖)) := by ring
    calc |Nx⁻¹ - Ny⁻¹| * ‖Iy‖
        ≤ (Real.exp ‖B‖ * Real.exp ‖B‖ * (Real.exp ‖B‖ * (‖B‖ * ‖x - y‖))) * Real.exp ‖B‖ :=
          mul_le_mul hinvdiff hIynorm (norm_nonneg _) (by positivity)
      _ = Real.exp ‖B‖ * Real.exp ‖B‖ * (Real.exp ‖B‖ * (‖B‖ * ‖x - y‖)) * Real.exp ‖B‖ := rfl
  calc ‖Nx⁻¹ • (Ix - Iy) + (Nx⁻¹ - Ny⁻¹) • Iy‖
      ≤ ‖Nx⁻¹ • (Ix - Iy)‖ + ‖(Nx⁻¹ - Ny⁻¹) • Iy‖ := norm_add_le _ _
    _ ≤ Real.exp ‖B‖ * (Real.exp ‖B‖ * (‖B‖ * ‖x - y‖)) +
        Real.exp ‖B‖ * Real.exp ‖B‖ * (Real.exp ‖B‖ * (‖B‖ * ‖x - y‖)) * Real.exp ‖B‖ :=
        add_le_add hterm1 hterm2
    _ ≤ 2 * ‖B‖ * Real.exp (4 * ‖B‖) * ‖x - y‖ := by
        have hB : (0:ℝ) ≤ ‖B‖ := norm_nonneg _
        have hxy : (0:ℝ) ≤ ‖x - y‖ := norm_nonneg _
        have e1 : Real.exp ‖B‖ * Real.exp ‖B‖ = Real.exp (2 * ‖B‖) := by
          rw [← Real.exp_add]; ring_nf
        have e2 : Real.exp ‖B‖ * Real.exp ‖B‖ * Real.exp ‖B‖ * Real.exp ‖B‖
            = Real.exp (4 * ‖B‖) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
        have hle : Real.exp (2 * ‖B‖) ≤ Real.exp (4 * ‖B‖) :=
          Real.exp_le_exp.mpr (by nlinarith)
        nlinarith [Real.exp_pos (2 * ‖B‖), Real.exp_pos (4 * ‖B‖),
          mul_nonneg hB hxy, mul_nonneg (mul_nonneg hB hxy) (Real.exp_pos (4 * ‖B‖)).le]

end PointModulus

/-! ### Vector-valued Kantorovich-Rubinstein and the `W₁` diameter bound

The scalar KR bound (`ofReal_integral_sub_le_W1`) controls scalar test integrals by `W₁`; the
Picard iteration needs the same for the vector-valued attention integrands. The proof is the
same coupling argument with `norm_integral_le_integral_norm` in place of the scalar estimate.
ForMathlib candidate: the statement is generic (any Lipschitz map into a Banach space) modulo
this file's `Eucl d`-specific `W₁`. -/

section VectorKR

/-- **Vector Kantorovich-Rubinstein, per coupling.** For a `c`-Lipschitz `g : Eucl d → Eucl d`
and a coupling `π` of `(μ, ν)` with integrable cost, the vector dual pairing is bounded by
`c` times the plan's average distance. -/
theorem norm_integral_sub_le_transportCost {g : Eucl d → Eucl d} {c : ℝ≥0}
    (hg : LipschitzWith c g) {π : Measure (Eucl d × Eucl d)} {μ ν : Measure (Eucl d)}
    (hπ : IsCoupling π μ ν) (hgμ : Integrable g μ) (hgν : Integrable g ν)
    (hcost : Integrable (fun p => dist p.1 p.2) π) :
    ‖(∫ x, g x ∂μ) - ∫ x, g x ∂ν‖ ≤ c * ∫ p, dist p.1 p.2 ∂π := by
  obtain ⟨rfl, rfl⟩ := hπ
  have hμ : ∫ x, g x ∂π.fst = ∫ p, g p.1 ∂π :=
    integral_map measurable_fst.aemeasurable hgμ.aestronglyMeasurable
  have hν : ∫ x, g x ∂π.snd = ∫ p, g p.2 ∂π :=
    integral_map measurable_snd.aemeasurable hgν.aestronglyMeasurable
  have hg1 : Integrable (fun p => g p.1) π :=
    (integrable_map_measure hgμ.aestronglyMeasurable measurable_fst.aemeasurable).mp hgμ
  have hg2 : Integrable (fun p => g p.2) π :=
    (integrable_map_measure hgν.aestronglyMeasurable measurable_snd.aemeasurable).mp hgν
  rw [hμ, hν, ← integral_sub hg1 hg2]
  calc ‖∫ p, (g p.1 - g p.2) ∂π‖ ≤ ∫ p, ‖g p.1 - g p.2‖ ∂π :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ p, (c : ℝ) * dist p.1 p.2 ∂π := by
        refine integral_mono (hg1.sub hg2).norm (hcost.const_mul _) fun p => ?_
        simpa [dist_eq_norm] using hg.dist_le_mul p.1 p.2
    _ = c * ∫ p, dist p.1 p.2 ∂π := integral_const_mul _ _

/-- **Vector Kantorovich-Rubinstein for `W₁`.** For probability measures and an integrable
`c`-Lipschitz vector integrand, `‖∫ g dμ - ∫ g dν‖ ≤ c · W₁(μ, ν)` (in `ℝ≥0∞`). -/
theorem ofReal_norm_integral_sub_le_W1 {g : Eucl d → Eucl d} {c : ℝ≥0}
    (hg : LipschitzWith c g) {μ ν : Measure (Eucl d)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hgμ : Integrable g μ) (hgν : Integrable g ν) :
    ENNReal.ofReal ‖(∫ x, g x ∂μ) - ∫ x, g x ∂ν‖ ≤ (c : ℝ≥0∞) * W1 μ ν := by
  rcases eq_or_ne c 0 with rfl | hc
  · -- A `0`-Lipschitz map is constant; probability masses agree, so the pairing vanishes.
    have hconst : ∀ x y : Eucl d, g x = g y := fun x y => by
      have := hg.dist_le_mul x y
      simpa [dist_le_zero] using this
    rcases isEmpty_or_nonempty (Eucl d) with hE | ⟨⟨x₀⟩⟩
    · simp [integral_of_isEmpty]
    · have hgx : g = fun _ => g x₀ := funext fun x => hconst x x₀
      rw [hgx]
      simp
  · -- Distribute `↑c` through the outer infimum (the only obligation is the vacuous `↑c = ⊤`),
    -- then collapse the inner coupling-indexed infimum: `transportCost π` when `π` is a coupling,
    -- else `↑c * ⊤ = ⊤` (using `↑c ≠ 0`).
    rw [W1, ENNReal.mul_iInf (fun h => absurd h ENNReal.coe_ne_top)]
    refine le_iInf fun π => ?_
    by_cases hπ : IsCoupling π μ ν
    case neg => rw [iInf_neg hπ, ENNReal.mul_top (by exact_mod_cast hc)]; exact le_top
    rw [iInf_pos hπ]
    rcases eq_or_ne (transportCost π) ⊤ with hfin | hfin
    · rw [hfin, ENNReal.mul_top (by exact_mod_cast hc)]
      exact le_top
    have hnonneg : 0 ≤ᵐ[π] fun p => dist p.1 p.2 := ae_of_all _ fun _ => dist_nonneg
    have haesm : AEStronglyMeasurable (fun p : Eucl d × Eucl d => dist p.1 p.2) π :=
      continuous_dist.aestronglyMeasurable
    have hlint : ∫⁻ p, ENNReal.ofReal (dist p.1 p.2) ∂π = transportCost π :=
      lintegral_congr fun p => (edist_dist p.1 p.2).symm
    have hcost : Integrable (fun p => dist p.1 p.2) π := by
      refine ⟨haesm, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal hnonneg, hlint]
      exact lt_top_iff_ne_top.mpr hfin
    calc ENNReal.ofReal ‖(∫ x, g x ∂μ) - ∫ x, g x ∂ν‖
        ≤ ENNReal.ofReal ((c : ℝ) * ∫ p, dist p.1 p.2 ∂π) :=
          ENNReal.ofReal_le_ofReal
            (norm_integral_sub_le_transportCost hg hπ hgμ hgν hcost)
      _ = (c : ℝ≥0∞) * ENNReal.ofReal (∫ p, dist p.1 p.2 ∂π) := by
          rw [ENNReal.ofReal_mul c.coe_nonneg]
          simp
      _ = (c : ℝ≥0∞) * transportCost π := by
          rw [ofReal_integral_eq_lintegral_ofReal hcost hnonneg, hlint]

/-- **`W₁` diameter bound.** Probability measures a.e.-supported in the ball of radius `R` are
within `W₁`-distance `2R` (via the product coupling); in particular sphere-supported pairs have
`W₁ ≤ 2 < ⊤`. -/
theorem W1_le_of_ae_norm_le (μ ν : Measure (Eucl d)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {R : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ R) (hν : ∀ᵐ y ∂ν, ‖y‖ ≤ R) :
    W1 μ ν ≤ ENNReal.ofReal (2 * R) := by
  refine le_trans (W1_le_transportCost (isCoupling_prod μ ν)) ?_
  have hae : ∀ᵐ p ∂(μ.prod ν), edist p.1 p.2 ≤ ENNReal.ofReal (2 * R) := by
    have h1 : ∀ᵐ p ∂(μ.prod ν), ‖p.1‖ ≤ R := Measure.quasiMeasurePreserving_fst.ae hμ
    have h2 : ∀ᵐ p ∂(μ.prod ν), ‖p.2‖ ≤ R := Measure.quasiMeasurePreserving_snd.ae hν
    filter_upwards [h1, h2] with p hp1 hp2
    rw [edist_dist]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [dist_eq_norm]
    calc ‖p.1 - p.2‖ ≤ ‖p.1‖ + ‖p.2‖ := norm_sub_le _ _
      _ ≤ 2 * R := by linarith
  calc transportCost (μ.prod ν) = ∫⁻ p, edist p.1 p.2 ∂(μ.prod ν) := rfl
    _ ≤ ∫⁻ _, ENNReal.ofReal (2 * R) ∂(μ.prod ν) := lintegral_mono_ae hae
    _ = ENNReal.ofReal (2 * R) := by simp

/-- Sphere-supported probability measures are within `W₁ ≤ 2`, in particular at finite `W₁`. -/
theorem W1_ne_top_of_sphere_supported (μ ν : Measure (Eucl d)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : μ (sphere d)ᶜ = 0) (hν : ν (sphere d)ᶜ = 0) :
    W1 μ ν ≠ ⊤ := by
  have hμa : ∀ᵐ x ∂μ, ‖x‖ ≤ 1 :=
    ae_of_sphere_supported hμ fun z hz => (norm_eq_one_of_mem_sphere hz).le
  have hνa : ∀ᵐ y ∂ν, ‖y‖ ≤ 1 :=
    ae_of_sphere_supported hν fun z hz => (norm_eq_one_of_mem_sphere hz).le
  exact ne_top_of_le_ne_top (by simp) (W1_le_of_ae_norm_le μ ν hμa hνa)

end VectorKR

end MeasureToMeasure.Foundations
