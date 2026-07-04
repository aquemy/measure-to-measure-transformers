import MeasureToMeasure.Foundations.AttentionEstimates

/-!
# Lipschitz-in-measure modulus of the self-attention field (milestone M3b)

The McKean-Vlasov well-posedness axioms `exists_meanFieldFlow` / `meanFieldFlow_unique` of
`Foundations/Attention.lean` are the Picard-Lindelöf / Grönwall consequences of the velocity field
(1.2) being Lipschitz jointly in the *point* `x` and the *measure* `μ` (for the `W₁` metric). The
point modulus is `AttentionEstimates.attnAvg_sub_le_of_norm_le`; the vector Kantorovich-Rubinstein
machinery (`ofReal_norm_integral_sub_le_W1`) is the tool for the measure modulus.

This file discharges the **full measure modulus**, kernel-clean, in two layers.

*Structural layer* (unconditional):
* `field_sub_measure_eq` — the field difference at a fixed point sees the measure only through the
  self-attention average: `field μ x - field ν x = P_x^⊥ (V (A_B[μ]x - A_B[ν]x))`. The perceptron
  term `W (U x + b)₊` is measure-independent, so it cancels exactly.
* `norm_field_sub_measure_le` — hence `‖field μ x - field ν x‖ ≤ ‖V‖ · ‖A_B[μ]x - A_B[ν]x‖` on the
  sphere, because the tangential projector is nonexpansive (`norm_tangentialProjector_le`).

*Analytic layer* (sphere-supported probability measures): the `MeasureModulus` section closes the
estimate the M3b groundwork isolated as its "Remaining for M3b" obstruction. The softmax integrands
`z ↦ e^{⟪Bx,z⟫}`, `z ↦ e^{⟪Bx,z⟫} • z` are not globally Lipschitz, so the vector Kantorovich–
Rubinstein tool does not apply verbatim; but the measures are sphere-supported, so every coupling is
concentrated on `sphere × sphere` and an **on-sphere** Lipschitz bound suffices
(`norm_integral_sub_le_transportCost_onSphere`, `..._W1_onSphere`, `..._W1_toReal_onSphere`, stated
for an arbitrary Banach codomain so the scalar denominator and vector numerator share one lemma).
Assembling the numerator/denominator moduli through the softmax quotient gives:
* `attnAvg_sub_measure_le` — `‖A_B[μ]x - A_B[ν]x‖ ≤ (e^{2‖B‖}+e^{4‖B‖})(1+‖B‖)·(W₁ μ ν).toReal`;
* `norm_field_sub_measure_W1_le` — `‖field μ x - field ν x‖ ≤ ‖V‖·(e^{2‖B‖}+e^{4‖B‖})(1+‖B‖)·W₁`.

With the point modulus (`AttentionEstimates.attnAvg_sub_le_of_norm_le`) this is the *complete*
Lipschitz-in-(point, `W₁`) modulus of the velocity field, so the **analytic** content of the
McKean-Vlasov well-posedness axioms is discharged.

*Coupling layer* (`CouplingBound` section): the last *measure-theoretic* ingredient of the
uniqueness Grönwall — `W1_map_le_lintegral_edist` / `W1_toReal_map_le_integral_norm`, the `W₁`
analogue of `Axioms.W2_map_le_L2`, bounding `W₁(f_#μ, g_#μ)` by the `μ`-average displacement
`∫ ‖f − g‖ ∂μ` via the plan `(f, g)_# μ`. Applied to the flow slices this dominates
`W₁((Φ_t)_#μ₀, (Ψ_t)_#μ₀)` by `∫ ‖Φ_t − Ψ_t‖ ∂μ₀`, the coupling step of the uniqueness argument.

So both the analytic moduli and the measure-coupling bound are now machine-checked. What remains for
`exists_meanFieldFlow` / `meanFieldFlow_unique` is purely the ODE-theoretic assembly (an FTC
representation of the flow trajectory — whose velocity's time-continuity the `deriv` clause does not
carry — plus an integral Grönwall and an a.e.-to-everywhere transfer), which Mathlib `v4.31.0`
cannot express directly for the measure-coupled field.
-/

namespace MeasureToMeasure.Foundations

open MeasureTheory MeasureToMeasure
open scoped RealInnerProductSpace ENNReal NNReal

variable {d : ℕ}

/-- The tangential projector is linear in the vector argument (subtraction form). -/
theorem tangentialProjector_sub (x u w : Eucl d) :
    tangentialProjector x (u - w) = tangentialProjector x u - tangentialProjector x w := by
  simp only [tangentialProjector_apply, inner_sub_right, sub_smul]
  abel

/-- **The tangential projector is nonexpansive at a unit vector:** `‖P_x^⊥ v‖ ≤ ‖v‖` for
`x ∈ 𝕊^{d-1}`. `P_x^⊥` is the orthogonal projection onto `{x}^⊥`, so it never increases norm;
concretely `‖P_x^⊥ v‖² = ‖v‖² - ⟪x, v⟫² ≤ ‖v‖²`. -/
theorem norm_tangentialProjector_le {x : Eucl d} (hx : x ∈ sphere d) (v : Eucl d) :
    ‖tangentialProjector x v‖ ≤ ‖v‖ := by
  -- `P_x^⊥ v ⟂ x`, so `⟪P_x^⊥ v, P_x^⊥ v⟫ = ⟪P_x^⊥ v, v⟫ = ‖v‖² - ⟪x,v⟫²`.
  have hperp : ⟪tangentialProjector x v, x⟫ = 0 := by
    rw [tangentialProjector_symm, tangentialProjector_self hx, inner_zero_right]
  have hself : ⟪tangentialProjector x v, tangentialProjector x v⟫
      = ⟪tangentialProjector x v, v⟫ := by
    nth_rewrite 2 [tangentialProjector_apply x v]
    rw [inner_sub_right, real_inner_smul_right, hperp, mul_zero, sub_zero]
  have hsq : ‖tangentialProjector x v‖ ^ 2 = ‖v‖ ^ 2 - ⟪x, v⟫ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq (tangentialProjector x v), hself,
      projector_inner_sub_sq hx]
  have hle : ‖tangentialProjector x v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [hsq]; nlinarith [sq_nonneg (⟪x, v⟫ : ℝ)]
  exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg v) hle

/-- **The field difference at a fixed point is carried by the self-attention average.** The
perceptron term `W (U x + b)₊` does not depend on the measure, so it cancels:
`field μ x - field ν x = P_x^⊥ (V (A_B[μ] x - A_B[ν] x))`. -/
theorem field_sub_measure_eq (p : AttnParams d) (μ ν : Measure (Eucl d)) (x : Eucl d) :
    p.field μ x - p.field ν x
      = tangentialProjector x (p.V (attnAvg p.B μ x - attnAvg p.B ν x)) := by
  simp only [AttnParams.field]
  rw [← tangentialProjector_sub]
  congr 1
  rw [map_sub p.V]
  abel

/-- **Structural measure modulus of the field.** On the sphere the field is Lipschitz in the
measure with the self-attention average's own modulus, scaled by the value matrix:
`‖field μ x - field ν x‖ ≤ ‖V‖ · ‖A_B[μ] x - A_B[ν] x‖`. Combined with a bound
`‖A_B[μ] x - A_B[ν] x‖ ≲ W₁(μ, ν)` (the remaining analytic estimate) this is the Lipschitz-in-`W₁`
modulus a McKean-Vlasov argument needs. -/
theorem norm_field_sub_measure_le (p : AttnParams d) (μ ν : Measure (Eucl d)) {x : Eucl d}
    (hx : x ∈ sphere d) :
    ‖p.field μ x - p.field ν x‖ ≤ ‖p.V‖ * ‖attnAvg p.B μ x - attnAvg p.B ν x‖ := by
  rw [field_sub_measure_eq]
  calc ‖tangentialProjector x (p.V (attnAvg p.B μ x - attnAvg p.B ν x))‖
      ≤ ‖p.V (attnAvg p.B μ x - attnAvg p.B ν x)‖ := norm_tangentialProjector_le hx _
    _ ≤ ‖p.V‖ * ‖attnAvg p.B μ x - attnAvg p.B ν x‖ := p.V.le_opNorm _

/-! ### The measure modulus: `μ ↦ A_B[μ](x)` is Lipschitz in `W₁`

The softmax integrands `z ↦ e^{⟪Bx,z⟫}` and `z ↦ e^{⟪Bx,z⟫} • z` are not globally Lipschitz, so the
Kantorovich–Rubinstein tool of `AttentionEstimates` (`ofReal_norm_integral_sub_le_W1`, which needs a
*global* Lipschitz constant) does not apply verbatim — this is the obstruction the M3b groundwork
flagged as unresolved. The resolution: the measures are sphere-supported, so *every* coupling is
`π`-a.e. concentrated on `sphere × sphere`, and an **on-sphere** Lipschitz bound is all the pairing
needs. This section proves the on-sphere KR variants and assembles the `W₁`-modulus of `attnAvg`,
closing that analytic obstruction. -/

section MeasureModulus

variable (B : Eucl d →L[ℝ] Eucl d) {μ ν : Measure (Eucl d)} {x : Eucl d}

/-- A coupling of two sphere-supported measures is `π`-a.e. concentrated on `sphere × sphere`. -/
theorem ae_mem_sphere_of_coupling {π : Measure (Eucl d × Eucl d)} {μ ν : Measure (Eucl d)}
    (hπ : IsCoupling π μ ν) (hμS : μ (sphere d)ᶜ = 0) (hνS : ν (sphere d)ᶜ = 0) :
    ∀ᵐ p ∂π, p.1 ∈ sphere d ∧ p.2 ∈ sphere d := by
  obtain ⟨hfst, hsnd⟩ := hπ
  have hmeas : MeasurableSet (sphere d)ᶜ := (Metric.isClosed_sphere.measurableSet).compl
  have h1 : ∀ᵐ p ∂π, p.1 ∈ sphere d := by
    have hpre : π (Prod.fst ⁻¹' (sphere d)ᶜ) = 0 := by
      rw [← Measure.fst_apply hmeas, hfst]; exact hμS
    rw [ae_iff]
    refine measure_mono_null (fun p hp => ?_) hpre
    simpa [Set.mem_preimage, Set.mem_compl_iff] using hp
  have h2 : ∀ᵐ p ∂π, p.2 ∈ sphere d := by
    have hpre : π (Prod.snd ⁻¹' (sphere d)ᶜ) = 0 := by
      rw [← Measure.snd_apply hmeas, hsnd]; exact hνS
    rw [ae_iff]
    refine measure_mono_null (fun p hp => ?_) hpre
    simpa [Set.mem_preimage, Set.mem_compl_iff] using hp
  filter_upwards [h1, h2] with p hp1 hp2 using ⟨hp1, hp2⟩

/-- **Vector Kantorovich–Rubinstein, per coupling, on the sphere.** For `g` Lipschitz *on the
sphere* with constant `c` and a coupling `π` of two sphere-supported measures, the vector dual
pairing is bounded by `c` times the plan's average distance. Only the on-sphere Lipschitz bound is
used, because `π` sits on `sphere × sphere`. -/
theorem norm_integral_sub_le_transportCost_onSphere {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : Eucl d → F} {c : ℝ}
    (hg : ∀ z ∈ sphere d, ∀ w ∈ sphere d, ‖g z - g w‖ ≤ c * dist z w)
    {π : Measure (Eucl d × Eucl d)} {μ ν : Measure (Eucl d)}
    (hπ : IsCoupling π μ ν) (hμS : μ (sphere d)ᶜ = 0) (hνS : ν (sphere d)ᶜ = 0)
    (hgμ : Integrable g μ) (hgν : Integrable g ν)
    (hcost : Integrable (fun p => dist p.1 p.2) π) :
    ‖(∫ x, g x ∂μ) - ∫ x, g x ∂ν‖ ≤ c * ∫ p, dist p.1 p.2 ∂π := by
  have hsupp := ae_mem_sphere_of_coupling hπ hμS hνS
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
    _ ≤ ∫ p, c * dist p.1 p.2 ∂π := by
        refine integral_mono_ae (hg1.sub hg2).norm (hcost.const_mul _) ?_
        filter_upwards [hsupp] with p hp using hg p.1 hp.1 p.2 hp.2
    _ = c * ∫ p, dist p.1 p.2 ∂π := integral_const_mul _ _

/-- **Vector Kantorovich–Rubinstein for `W₁`, on the sphere.** For sphere-supported probability
measures and a `g` that is `c`-Lipschitz on the sphere (`0 < c`), the vector pairing is bounded by
`c · W₁(μ, ν)`. -/
theorem ofReal_norm_integral_sub_le_W1_onSphere {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : Eucl d → F} {c : ℝ} (hc : 0 < c)
    (hg : ∀ z ∈ sphere d, ∀ w ∈ sphere d, ‖g z - g w‖ ≤ c * dist z w)
    {μ ν : Measure (Eucl d)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμS : μ (sphere d)ᶜ = 0) (hνS : ν (sphere d)ᶜ = 0)
    (hgμ : Integrable g μ) (hgν : Integrable g ν) :
    ENNReal.ofReal ‖(∫ x, g x ∂μ) - ∫ x, g x ∂ν‖ ≤ ENNReal.ofReal c * W1 μ ν := by
  rw [W1, ENNReal.mul_iInf (fun h => absurd h ENNReal.ofReal_ne_top)]
  refine le_iInf fun π => ?_
  by_cases hπ : IsCoupling π μ ν
  case neg => rw [iInf_neg hπ, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hc).ne']; exact le_top
  rw [iInf_pos hπ]
  rcases eq_or_ne (transportCost π) ⊤ with hfin | hfin
  · rw [hfin, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hc).ne']; exact le_top
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
      ≤ ENNReal.ofReal (c * ∫ p, dist p.1 p.2 ∂π) :=
        ENNReal.ofReal_le_ofReal
          (norm_integral_sub_le_transportCost_onSphere hg hπ hμS hνS hgμ hgν hcost)
    _ = ENNReal.ofReal c * ENNReal.ofReal (∫ p, dist p.1 p.2 ∂π) := by
        rw [ENNReal.ofReal_mul hc.le]
    _ = ENNReal.ofReal c * transportCost π := by
        rw [ofReal_integral_eq_lintegral_ofReal hcost hnonneg, hlint]

/-- Real-valued on-sphere Kantorovich–Rubinstein: for sphere-supported probability measures at
finite `W₁` and a `g` that is `c`-Lipschitz on the sphere, `‖∫g dμ - ∫g dν‖ ≤ c · (W₁ μ ν).toReal`.
-/
theorem norm_integral_sub_le_W1_toReal_onSphere {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : Eucl d → F} {c : ℝ} (hc : 0 < c)
    (hg : ∀ z ∈ sphere d, ∀ w ∈ sphere d, ‖g z - g w‖ ≤ c * dist z w)
    {μ ν : Measure (Eucl d)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμS : μ (sphere d)ᶜ = 0) (hνS : ν (sphere d)ᶜ = 0) (hW1 : W1 μ ν ≠ ⊤)
    (hgμ : Integrable g μ) (hgν : Integrable g ν) :
    ‖(∫ x, g x ∂μ) - ∫ x, g x ∂ν‖ ≤ c * (W1 μ ν).toReal := by
  have hEN := ofReal_norm_integral_sub_le_W1_onSphere hc hg hμS hνS hgμ hgν
  have hfin : ENNReal.ofReal c * W1 μ ν ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hW1
  have hmono := (ENNReal.toReal_le_toReal (by simp) hfin).mpr hEN
  rwa [ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hc.le] at hmono

/-- **The measure modulus of the self-attention average.** For sphere-supported probability
measures at finite `W₁` and a point of the unit ball, `A_B[·](x)` is Lipschitz in the measure for
the `W₁` metric:
`‖A_B[μ](x) - A_B[ν](x)‖ ≤ (e^{2‖B‖} + e^{4‖B‖})(1 + ‖B‖) · (W₁ μ ν).toReal`.
This is the estimate the M3b groundwork (`AttentionEstimates`, "Remaining for M3b") isolated as the
last analytic obstruction to the mean-field well-posedness axioms — the softmax integrands are only
Lipschitz on the sphere, which the on-sphere Kantorovich–Rubinstein bound above handles because the
measures are sphere-supported. -/
theorem attnAvg_sub_measure_le (B : Eucl d →L[ℝ] Eucl d) {μ ν : Measure (Eucl d)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμS : μ (sphere d)ᶜ = 0) (hνS : ν (sphere d)ᶜ = 0) (hW1 : W1 μ ν ≠ ⊤)
    {x : Eucl d} (hx : ‖x‖ ≤ 1) :
    ‖attnAvg B μ x - attnAvg B ν x‖ ≤
      (Real.exp (2 * ‖B‖) + Real.exp (4 * ‖B‖)) * (1 + ‖B‖) * (W1 μ ν).toReal := by
  set W1t := (W1 μ ν).toReal with hW1t
  have hW1t0 : 0 ≤ W1t := ENNReal.toReal_nonneg
  set c : ℝ := Real.exp ‖B‖ * (1 + ‖B‖) with hcdef
  have hcpos : 0 < c := by positivity
  set Nμ := ∫ z, Real.exp ⟪B x, z⟫ ∂μ with hNμ
  set Nν := ∫ z, Real.exp ⟪B x, z⟫ ∂ν with hNν
  set Iμ := ∫ z, Real.exp ⟪B x, z⟫ • z ∂μ with hIμ
  set Iν := ∫ z, Real.exp ⟪B x, z⟫ • z ∂ν with hIν
  have hNμpos : (0:ℝ) < Nμ := lt_of_lt_of_le (Real.exp_pos _) (denom_ge_exp_neg B hμS hx)
  have hNνpos : (0:ℝ) < Nν := lt_of_lt_of_le (Real.exp_pos _) (denom_ge_exp_neg B hνS hx)
  have hNμinv : Nμ⁻¹ ≤ Real.exp ‖B‖ := by
    rw [inv_le_comm₀ hNμpos (Real.exp_pos _)]
    calc (Real.exp ‖B‖)⁻¹ = Real.exp (-‖B‖) := (Real.exp_neg _).symm
      _ ≤ Nμ := denom_ge_exp_neg B hμS hx
  have hNνinv : Nν⁻¹ ≤ Real.exp ‖B‖ := by
    rw [inv_le_comm₀ hNνpos (Real.exp_pos _)]
    calc (Real.exp ‖B‖)⁻¹ = Real.exp (-‖B‖) := (Real.exp_neg _).symm
      _ ≤ Nν := denom_ge_exp_neg B hνS hx
  have hIνnorm : ‖Iν‖ ≤ Real.exp ‖B‖ := norm_num_integral_le B hνS hx
  have hBx : ‖B x‖ ≤ ‖B‖ :=
    (B.le_opNorm x).trans (by simpa using mul_le_mul_of_nonneg_left hx (norm_nonneg B))
  -- On-sphere Lipschitz of the (scalar) denominator integrand, with the common constant `c`.
  have hker : ∀ z ∈ sphere d, ∀ w ∈ sphere d,
      ‖Real.exp ⟪B x, z⟫ - Real.exp ⟪B x, w⟫‖ ≤ c * dist z w := by
    intro z hz w hw
    rw [Real.norm_eq_abs]
    have ha : ⟪B x, z⟫ ≤ ‖B‖ := (le_abs_self _).trans (abs_inner_attn_le B hx hz)
    have hb : ⟪B x, w⟫ ≤ ‖B‖ := (le_abs_self _).trans (abs_inner_attn_le B hx hw)
    have hdiff : |⟪B x, z⟫ - ⟪B x, w⟫| ≤ ‖B‖ * dist z w := by
      have hrw : (⟪B x, z⟫ : ℝ) - ⟪B x, w⟫ = ⟪B x, z - w⟫ := (inner_sub_right _ _ _).symm
      rw [hrw, dist_eq_norm]
      calc |⟪B x, z - w⟫| ≤ ‖B x‖ * ‖z - w‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖B‖ * ‖z - w‖ := by gcongr
    calc |Real.exp ⟪B x, z⟫ - Real.exp ⟪B x, w⟫|
        ≤ Real.exp ‖B‖ * |⟪B x, z⟫ - ⟪B x, w⟫| := abs_exp_sub_exp_le ha hb
      _ ≤ Real.exp ‖B‖ * (‖B‖ * dist z w) := by gcongr
      _ ≤ Real.exp ‖B‖ * (1 + ‖B‖) * dist z w := by
          have hd : (0:ℝ) ≤ dist z w := dist_nonneg
          nlinarith [mul_nonneg (Real.exp_pos ‖B‖).le hd]
  -- On-sphere Lipschitz of the (vector) numerator integrand, same constant.
  have hnum : ∀ z ∈ sphere d, ∀ w ∈ sphere d,
      ‖Real.exp ⟪B x, z⟫ • z - Real.exp ⟪B x, w⟫ • w‖ ≤ c * dist z w := by
    intro z hz w hw
    have hwn : ‖w‖ = 1 := norm_eq_one_of_mem_sphere hw
    have haz : |Real.exp ⟪B x, z⟫| ≤ Real.exp ‖B‖ := by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (abs_inner_attn_le B hx hz))
    have hkerzw : |Real.exp ⟪B x, z⟫ - Real.exp ⟪B x, w⟫| ≤ Real.exp ‖B‖ * ‖B‖ * dist z w := by
      have ha : ⟪B x, z⟫ ≤ ‖B‖ := (le_abs_self _).trans (abs_inner_attn_le B hx hz)
      have hb : ⟪B x, w⟫ ≤ ‖B‖ := (le_abs_self _).trans (abs_inner_attn_le B hx hw)
      have hdiff : |⟪B x, z⟫ - ⟪B x, w⟫| ≤ ‖B‖ * dist z w := by
        have hrw : (⟪B x, z⟫ : ℝ) - ⟪B x, w⟫ = ⟪B x, z - w⟫ := (inner_sub_right _ _ _).symm
        rw [hrw, dist_eq_norm]
        calc |⟪B x, z - w⟫| ≤ ‖B x‖ * ‖z - w‖ := abs_real_inner_le_norm _ _
          _ ≤ ‖B‖ * ‖z - w‖ := by gcongr
      calc |Real.exp ⟪B x, z⟫ - Real.exp ⟪B x, w⟫|
          ≤ Real.exp ‖B‖ * |⟪B x, z⟫ - ⟪B x, w⟫| := abs_exp_sub_exp_le ha hb
        _ ≤ Real.exp ‖B‖ * (‖B‖ * dist z w) := by gcongr
        _ = Real.exp ‖B‖ * ‖B‖ * dist z w := by ring
    have hsplit : Real.exp ⟪B x, z⟫ • z - Real.exp ⟪B x, w⟫ • w
        = Real.exp ⟪B x, z⟫ • (z - w) + (Real.exp ⟪B x, z⟫ - Real.exp ⟪B x, w⟫) • w := by
      rw [smul_sub, sub_smul]; abel
    rw [hsplit, hcdef]
    calc ‖Real.exp ⟪B x, z⟫ • (z - w) + (Real.exp ⟪B x, z⟫ - Real.exp ⟪B x, w⟫) • w‖
        ≤ ‖Real.exp ⟪B x, z⟫ • (z - w)‖ + ‖(Real.exp ⟪B x, z⟫ - Real.exp ⟪B x, w⟫) • w‖ :=
          norm_add_le _ _
      _ = |Real.exp ⟪B x, z⟫| * ‖z - w‖ +
            |Real.exp ⟪B x, z⟫ - Real.exp ⟪B x, w⟫| * ‖w‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ Real.exp ‖B‖ * dist z w + (Real.exp ‖B‖ * ‖B‖ * dist z w) * 1 := by
          rw [hwn, dist_eq_norm]; gcongr; exact hkerzw
      _ = Real.exp ‖B‖ * (1 + ‖B‖) * dist z w := by ring
  -- Numerator and denominator `W₁`-moduli.
  have hnumW1 : ‖Iμ - Iν‖ ≤ c * W1t :=
    norm_integral_sub_le_W1_toReal_onSphere hcpos hnum hμS hνS hW1
      (integrable_attnKernel_smul B hμS hx) (integrable_attnKernel_smul B hνS hx)
  have hdenW1 : |Nμ - Nν| ≤ c * W1t := by
    have h := norm_integral_sub_le_W1_toReal_onSphere (F := ℝ) hcpos hker hμS hνS hW1
      (integrable_attnKernel B hμS hx) (integrable_attnKernel B hνS hx)
    simpa [Real.norm_eq_abs] using h
  -- Split through the mid-point `Nμ⁻¹ • Iν`.
  have hsplit : attnAvg B μ x - attnAvg B ν x
      = Nμ⁻¹ • (Iμ - Iν) + (Nμ⁻¹ - Nν⁻¹) • Iν := by
    rw [attnAvg, attnAvg, ← hNμ, ← hNν, ← hIμ, ← hIν, smul_sub, sub_smul]; abel
  have hterm1 : ‖Nμ⁻¹ • (Iμ - Iν)‖ ≤ Real.exp ‖B‖ * (c * W1t) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hNμpos)]
    exact mul_le_mul hNμinv hnumW1 (norm_nonneg _) (Real.exp_pos _).le
  have hterm2 : ‖(Nμ⁻¹ - Nν⁻¹) • Iν‖ ≤ Real.exp (3 * ‖B‖) * (c * W1t) := by
    rw [norm_smul, Real.norm_eq_abs]
    have hinvdiff : |Nμ⁻¹ - Nν⁻¹| ≤ Real.exp (2 * ‖B‖) * (c * W1t) := by
      have hrw : Nμ⁻¹ - Nν⁻¹ = (Nν - Nμ) * (Nμ⁻¹ * Nν⁻¹) := by field_simp
      rw [hrw, abs_mul]
      have h1 : |Nν - Nμ| ≤ c * W1t := by rw [abs_sub_comm]; exact hdenW1
      have h2 : |Nμ⁻¹ * Nν⁻¹| ≤ Real.exp (2 * ‖B‖) := by
        rw [abs_mul, abs_of_pos (inv_pos.mpr hNμpos), abs_of_pos (inv_pos.mpr hNνpos)]
        calc Nμ⁻¹ * Nν⁻¹ ≤ Real.exp ‖B‖ * Real.exp ‖B‖ :=
              mul_le_mul hNμinv hNνinv (inv_pos.mpr hNνpos).le (Real.exp_pos _).le
          _ = Real.exp (2 * ‖B‖) := by rw [← Real.exp_add]; ring_nf
      calc |Nν - Nμ| * |Nμ⁻¹ * Nν⁻¹| ≤ (c * W1t) * Real.exp (2 * ‖B‖) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = Real.exp (2 * ‖B‖) * (c * W1t) := by ring
    calc |Nμ⁻¹ - Nν⁻¹| * ‖Iν‖ ≤ (Real.exp (2 * ‖B‖) * (c * W1t)) * Real.exp ‖B‖ :=
          mul_le_mul hinvdiff hIνnorm (norm_nonneg _) (by positivity)
      _ = Real.exp (3 * ‖B‖) * (c * W1t) := by
          rw [mul_comm, ← mul_assoc, ← Real.exp_add]; ring_nf
  rw [hsplit]
  calc ‖Nμ⁻¹ • (Iμ - Iν) + (Nμ⁻¹ - Nν⁻¹) • Iν‖
      ≤ ‖Nμ⁻¹ • (Iμ - Iν)‖ + ‖(Nμ⁻¹ - Nν⁻¹) • Iν‖ := norm_add_le _ _
    _ ≤ Real.exp ‖B‖ * (c * W1t) + Real.exp (3 * ‖B‖) * (c * W1t) := add_le_add hterm1 hterm2
    _ = (Real.exp (2 * ‖B‖) + Real.exp (4 * ‖B‖)) * (1 + ‖B‖) * W1t := by
        have e2 : Real.exp ‖B‖ * Real.exp ‖B‖ = Real.exp (2 * ‖B‖) := by
          rw [← Real.exp_add]; ring_nf
        have e4 : Real.exp (3 * ‖B‖) * Real.exp ‖B‖ = Real.exp (4 * ‖B‖) := by
          rw [← Real.exp_add]; ring_nf
        rw [hcdef, ← e2, ← e4]; ring

/-- **The `W₁`-modulus of the self-attention field.** Combining the structural reduction
`norm_field_sub_measure_le` (perceptron cancels, projector nonexpansive) with the average's measure
modulus, the field itself is Lipschitz in the measure for `W₁`:
`‖field μ x - field ν x‖ ≤ ‖V‖·(e^{2‖B‖}+e^{4‖B‖})(1+‖B‖)·(W₁ μ ν).toReal`. This is the complete
measure-side modulus a McKean–Vlasov Grönwall/Picard argument consumes; with the point modulus
(`AttentionEstimates.attnAvg_sub_le_of_norm_le`) it closes the *analytic* half of mean-field
well-posedness, leaving only the ODE-theoretic assembly (a Grönwall in the joint (point, `W₁`)
variable). -/
theorem norm_field_sub_measure_W1_le (p : AttnParams d) {μ ν : Measure (Eucl d)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμS : μ (sphere d)ᶜ = 0) (hνS : ν (sphere d)ᶜ = 0) (hW1 : W1 μ ν ≠ ⊤)
    {x : Eucl d} (hx : x ∈ sphere d) :
    ‖p.field μ x - p.field ν x‖ ≤
      ‖p.V‖ * ((Real.exp (2 * ‖p.B‖) + Real.exp (4 * ‖p.B‖)) * (1 + ‖p.B‖)) * (W1 μ ν).toReal := by
  have hxb : ‖x‖ ≤ 1 := (norm_eq_one_of_mem_sphere hx).le
  calc ‖p.field μ x - p.field ν x‖
      ≤ ‖p.V‖ * ‖attnAvg p.B μ x - attnAvg p.B ν x‖ := norm_field_sub_measure_le p μ ν hx
    _ ≤ ‖p.V‖ *
          ((Real.exp (2 * ‖p.B‖) + Real.exp (4 * ‖p.B‖)) * (1 + ‖p.B‖) * (W1 μ ν).toReal) := by
        gcongr
        exact attnAvg_sub_measure_le p.B hμS hνS hW1 hxb
    _ = ‖p.V‖ * ((Real.exp (2 * ‖p.B‖) + Real.exp (4 * ‖p.B‖)) * (1 + ‖p.B‖)) * (W1 μ ν).toReal := by
        ring

end MeasureModulus

/-! ### The measure-trajectory coupling bound

The final measure-theoretic ingredient of the mean-field uniqueness Grönwall. The `W₁` distance
between two pushforwards of a common measure `μ` is bounded by the `μ`-average displacement of the
two maps — the `W₁` analogue of `Axioms.W2_map_le_L2`, witnessed by the plan `(f, g)_# μ`, whose
transport cost is exactly that average displacement. Applied to the two flow slices `Φ_t, Ψ_t` and
`μ = μ₀` it turns the pointwise flow distance `∫ ‖Φ_t x − Ψ_t x‖ ∂μ₀` into a control on
`W₁((Φ_t)_#μ₀, (Ψ_t)_#μ₀)` — the coupling step that feeds the field's measure modulus in the
Grönwall estimate. -/

section CouplingBound

variable {μ : Measure (Eucl d)} {f g : Eucl d → Eucl d}

/-- **`W₁` map-coupling bound (`ℝ≥0∞` form).** The `W₁` distance between two pushforwards of `μ` is
at most the `μ`-average `edist` of the maps, witnessed by the plan `(f, g)_# μ`. -/
theorem W1_map_le_lintegral_edist (hf : Measurable f) (hg : Measurable g) :
    W1 (μ.map f) (μ.map g) ≤ ∫⁻ x, edist (f x) (g x) ∂μ := by
  have hcpl : IsCoupling (μ.map fun x => (f x, g x)) (μ.map f) (μ.map g) :=
    ⟨Measure.fst_map_prodMk hg, Measure.snd_map_prodMk hf⟩
  calc W1 (μ.map f) (μ.map g)
      ≤ transportCost (μ.map fun x => (f x, g x)) := W1_le_transportCost hcpl
    _ = ∫⁻ x, edist (f x) (g x) ∂μ := by
        rw [transportCost, lintegral_map (by fun_prop) (by fun_prop)]

/-- **`W₁` map-coupling bound (`ℝ` form).** For a `μ`-integrable displacement the real-valued `W₁`
between the two pushforwards is at most the average norm displacement `∫ ‖f x − g x‖ ∂μ`. This is the
bridge from the pointwise flow distance to `W₁` that the uniqueness Grönwall consumes. -/
theorem W1_toReal_map_le_integral_norm (hf : Measurable f) (hg : Measurable g)
    (hint : Integrable (fun x => ‖f x - g x‖) μ) :
    (W1 (μ.map f) (μ.map g)).toReal ≤ ∫ x, ‖f x - g x‖ ∂μ := by
  have hle := W1_map_le_lintegral_edist (μ := μ) hf hg
  have heq : ∫⁻ x, edist (f x) (g x) ∂μ = ENNReal.ofReal (∫ x, ‖f x - g x‖ ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => norm_nonneg _)]
    exact lintegral_congr fun x => by rw [edist_dist, dist_eq_norm]
  rw [heq] at hle
  rw [← ENNReal.toReal_ofReal (integral_nonneg fun x => norm_nonneg _)]
  exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hle

end CouplingBound

/-! ### The point modulus: `x ↦ field μ x` is Lipschitz on the sphere

The measure modulus (`norm_field_sub_measure_W1_le`) controls the field's dependence on `μ`; the
ODE-uniqueness step of mean-field well-posedness also needs its dependence on the *point* — the field
`field μ ·` Lipschitz on the sphere (the `LipschitzOnWith` hypothesis of `ODE_solution_unique`). The
self-attention average's point modulus lives in `AttentionEstimates.attnAvg_sub_le_of_norm_le`, but
the *field* wraps that average in the base-point-dependent projector `P_x^⊥` and adds the perceptron
term `W (U x + b)₊`, so the field's own point modulus is a genuine further step: the projector varies
with the base point (`norm_tangentialProjector_sub_point_le`) and the perceptron term is Lipschitz
through the nonexpansive coordinatewise ReLU (`norm_reluVec_sub_le`). -/

section PointModulus

/-- **The tangential projector is Lipschitz in its base point** (on the sphere):
`‖P_x^⊥ v - P_y^⊥ v‖ ≤ 2 ‖v‖ ‖x - y‖` for `x, y ∈ 𝕊^{d-1}`. Writing
`P_x^⊥ v - P_y^⊥ v = ⟪y - x, v⟫ y + ⟪x, v⟫ (y - x)` and bounding each inner product by Cauchy–Schwarz
with `‖x‖ = ‖y‖ = 1`. -/
theorem norm_tangentialProjector_sub_point_le {x y : Eucl d} (hx : x ∈ sphere d) (hy : y ∈ sphere d)
    (v : Eucl d) :
    ‖tangentialProjector x v - tangentialProjector y v‖ ≤ 2 * ‖v‖ * ‖x - y‖ := by
  have hxn : ‖x‖ = 1 := norm_eq_one_of_mem_sphere hx
  have hyn : ‖y‖ = 1 := norm_eq_one_of_mem_sphere hy
  have key : tangentialProjector x v - tangentialProjector y v
      = (⟪y - x, v⟫ : ℝ) • y + (⟪x, v⟫ : ℝ) • (y - x) := by
    simp only [tangentialProjector_apply, inner_sub_left, sub_smul, smul_sub]
    abel
  rw [key]
  have h1 : ‖(⟪y - x, v⟫ : ℝ) • y‖ ≤ ‖x - y‖ * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, hyn, mul_one]
    calc |(⟪y - x, v⟫ : ℝ)| ≤ ‖y - x‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ = ‖x - y‖ * ‖v‖ := by rw [norm_sub_rev]
  have h2 : ‖(⟪x, v⟫ : ℝ) • (y - x)‖ ≤ ‖v‖ * ‖x - y‖ := by
    rw [norm_smul, Real.norm_eq_abs, norm_sub_rev]
    have hxv : |(⟪x, v⟫ : ℝ)| ≤ ‖v‖ := by
      calc |(⟪x, v⟫ : ℝ)| ≤ ‖x‖ * ‖v‖ := abs_real_inner_le_norm _ _
        _ = ‖v‖ := by rw [hxn, one_mul]
    exact mul_le_mul_of_nonneg_right hxv (norm_nonneg _)
  calc ‖(⟪y - x, v⟫ : ℝ) • y + (⟪x, v⟫ : ℝ) • (y - x)‖
      ≤ ‖(⟪y - x, v⟫ : ℝ) • y‖ + ‖(⟪x, v⟫ : ℝ) • (y - x)‖ := norm_add_le _ _
    _ ≤ ‖x - y‖ * ‖v‖ + ‖v‖ * ‖x - y‖ := add_le_add h1 h2
    _ = 2 * ‖v‖ * ‖x - y‖ := by ring

/-- **Coordinatewise ReLU is nonexpansive:** `‖(a)₊ - (b)₊‖ ≤ ‖a - b‖`. Each coordinate
`t ↦ max 0 t` is `1`-Lipschitz (`abs_max_sub_max_le_abs`), so the `L²` norm cannot increase. -/
theorem norm_reluVec_sub_le (a b : Eucl d) : ‖reluVec a - reluVec b‖ ≤ ‖a - b‖ := by
  rw [EuclideanSpace.norm_eq (reluVec a - reluVec b), EuclideanSpace.norm_eq (a - b)]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  have h : |max 0 (a.ofLp i) - max 0 (b.ofLp i)| ≤ |a.ofLp i - b.ofLp i| := by
    rw [max_comm 0 (a.ofLp i), max_comm 0 (b.ofLp i)]
    exact abs_max_sub_max_le_abs _ _ _
  simp only [reluVec, WithLp.ofLp_sub, Real.norm_eq_abs, Pi.sub_apply]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

/-- **Coordinatewise ReLU is bounded by the identity:** `‖(a)₊‖ ≤ ‖a‖` (nonexpansiveness at
`b = 0`, since `(0)₊ = 0`). -/
theorem norm_reluVec_le (a : Eucl d) : ‖reluVec a‖ ≤ ‖a‖ := by
  have h0 : reluVec (0 : Eucl d) = 0 := by ext i; simp [reluVec]
  calc ‖reluVec a‖ = ‖reluVec a - reluVec 0‖ := by rw [h0, sub_zero]
    _ ≤ ‖a - 0‖ := norm_reluVec_sub_le a 0
    _ = ‖a‖ := by rw [sub_zero]

/-- **Point modulus of the field on the sphere.** For a fixed sphere-supported probability measure
`μ`, the field `field μ ·` is Lipschitz on `𝕊^{d-1}`: the attention average's point modulus
(`attnAvg_sub_le_of_norm_le`) drives the `V`-term, the nonexpansive coordinatewise ReLU
(`norm_reluVec_sub_le`) drives the perceptron term, and the projector's base-point Lipschitzness
(`norm_tangentialProjector_sub_point_le`) accounts for `P_x^⊥`'s own `x`-dependence (with the
argument bounded via `norm_attnAvg_le` / `norm_reluVec_le`). Together with the measure modulus
`norm_field_sub_measure_W1_le` this is the *complete* joint Lipschitz-in-`(point, W₁)` modulus of the
field — the `LipschitzOnWith` hypothesis on `field μ ·` that the mean-field uniqueness ODE argument
(`ODE_solution_unique`) consumes. -/
theorem norm_field_sub_point_le (p : AttnParams d) (μ : Measure (Eucl d)) [IsProbabilityMeasure μ]
    (hμS : μ (sphere d)ᶜ = 0) {x y : Eucl d} (hx : x ∈ sphere d) (hy : y ∈ sphere d) :
    ‖p.field μ x - p.field μ y‖ ≤
      ((‖p.V‖ * (2 * ‖p.B‖ * Real.exp (4 * ‖p.B‖)) + ‖p.W‖ * ‖p.U‖)
        + 2 * (‖p.V‖ * Real.exp (2 * ‖p.B‖) + ‖p.W‖ * (‖p.U‖ + ‖p.b‖))) * ‖x - y‖ := by
  have hxb : ‖x‖ ≤ 1 := (norm_eq_one_of_mem_sphere hx).le
  have hyb : ‖y‖ ≤ 1 := (norm_eq_one_of_mem_sphere hy).le
  set ax := p.V (attnAvg p.B μ x) + p.W (reluVec (p.U x + p.b)) with hax
  set ay := p.V (attnAvg p.B μ y) + p.W (reluVec (p.U y + p.b)) with hay
  have hfield : p.field μ x - p.field μ y
      = tangentialProjector x (ax - ay)
        + (tangentialProjector x ay - tangentialProjector y ay) := by
    simp only [AttnParams.field, hax, hay]
    rw [tangentialProjector_sub]
    abel
  -- `‖ax - ay‖` bound: attention point modulus + nonexpansive ReLU.
  have haxay : ‖ax - ay‖
      ≤ (‖p.V‖ * (2 * ‖p.B‖ * Real.exp (4 * ‖p.B‖)) + ‖p.W‖ * ‖p.U‖) * ‖x - y‖ := by
    have e1 : ax - ay = p.V (attnAvg p.B μ x - attnAvg p.B μ y)
        + p.W (reluVec (p.U x + p.b) - reluVec (p.U y + p.b)) := by
      simp only [hax, hay, map_sub]; abel
    have eU : (p.U x + p.b) - (p.U y + p.b) = p.U (x - y) := by rw [map_sub]; abel
    rw [e1]
    calc ‖p.V (attnAvg p.B μ x - attnAvg p.B μ y)
            + p.W (reluVec (p.U x + p.b) - reluVec (p.U y + p.b))‖
        ≤ ‖p.V (attnAvg p.B μ x - attnAvg p.B μ y)‖
            + ‖p.W (reluVec (p.U x + p.b) - reluVec (p.U y + p.b))‖ := norm_add_le _ _
      _ ≤ ‖p.V‖ * ‖attnAvg p.B μ x - attnAvg p.B μ y‖
            + ‖p.W‖ * ‖reluVec (p.U x + p.b) - reluVec (p.U y + p.b)‖ :=
          add_le_add (p.V.le_opNorm _) (p.W.le_opNorm _)
      _ ≤ ‖p.V‖ * (2 * ‖p.B‖ * Real.exp (4 * ‖p.B‖) * ‖x - y‖) + ‖p.W‖ * ‖p.U (x - y)‖ := by
          gcongr
          · exact attnAvg_sub_le_of_norm_le p.B hμS hxb hyb
          · rw [← eU]; exact norm_reluVec_sub_le _ _
      _ ≤ ‖p.V‖ * (2 * ‖p.B‖ * Real.exp (4 * ‖p.B‖) * ‖x - y‖) + ‖p.W‖ * (‖p.U‖ * ‖x - y‖) := by
          gcongr; exact p.U.le_opNorm _
      _ = (‖p.V‖ * (2 * ‖p.B‖ * Real.exp (4 * ‖p.B‖)) + ‖p.W‖ * ‖p.U‖) * ‖x - y‖ := by ring
  -- `‖ay‖` bound: attention average bounded + ReLU bounded.
  have hay_bd : ‖ay‖ ≤ ‖p.V‖ * Real.exp (2 * ‖p.B‖) + ‖p.W‖ * (‖p.U‖ + ‖p.b‖) := by
    calc ‖ay‖ ≤ ‖p.V (attnAvg p.B μ y)‖ + ‖p.W (reluVec (p.U y + p.b))‖ := by
            rw [hay]; exact norm_add_le _ _
      _ ≤ ‖p.V‖ * ‖attnAvg p.B μ y‖ + ‖p.W‖ * ‖reluVec (p.U y + p.b)‖ :=
          add_le_add (p.V.le_opNorm _) (p.W.le_opNorm _)
      _ ≤ ‖p.V‖ * Real.exp (2 * ‖p.B‖) + ‖p.W‖ * ‖p.U y + p.b‖ := by
          gcongr
          · exact norm_attnAvg_le p.B hμS hyb
          · exact norm_reluVec_le _
      _ ≤ ‖p.V‖ * Real.exp (2 * ‖p.B‖) + ‖p.W‖ * (‖p.U‖ + ‖p.b‖) := by
          gcongr
          calc ‖p.U y + p.b‖ ≤ ‖p.U y‖ + ‖p.b‖ := norm_add_le _ _
            _ ≤ ‖p.U‖ * ‖y‖ + ‖p.b‖ := by gcongr; exact p.U.le_opNorm _
            _ = ‖p.U‖ + ‖p.b‖ := by rw [norm_eq_one_of_mem_sphere hy, mul_one]
  rw [hfield]
  calc ‖tangentialProjector x (ax - ay)
          + (tangentialProjector x ay - tangentialProjector y ay)‖
      ≤ ‖tangentialProjector x (ax - ay)‖
          + ‖tangentialProjector x ay - tangentialProjector y ay‖ := norm_add_le _ _
    _ ≤ ‖ax - ay‖ + 2 * ‖ay‖ * ‖x - y‖ :=
        add_le_add (norm_tangentialProjector_le hx _) (norm_tangentialProjector_sub_point_le hx hy _)
    _ ≤ (‖p.V‖ * (2 * ‖p.B‖ * Real.exp (4 * ‖p.B‖)) + ‖p.W‖ * ‖p.U‖) * ‖x - y‖
          + 2 * (‖p.V‖ * Real.exp (2 * ‖p.B‖) + ‖p.W‖ * (‖p.U‖ + ‖p.b‖)) * ‖x - y‖ := by
        gcongr
    _ = ((‖p.V‖ * (2 * ‖p.B‖ * Real.exp (4 * ‖p.B‖)) + ‖p.W‖ * ‖p.U‖)
          + 2 * (‖p.V‖ * Real.exp (2 * ‖p.B‖) + ‖p.W‖ * (‖p.U‖ + ‖p.b‖))) * ‖x - y‖ := by ring

end PointModulus

/-! ### Integral-form Grönwall

The one ingredient the mean-field uniqueness argument needs that Mathlib `v4.31.0` does not package
directly: a Grönwall inequality for a *nonnegative continuous functional* obeying an *integral*
bound `h t ≤ K ∫₀ᵗ h`. The functional `h t = ∫ ‖Φ_t x − Ψ_t x‖ ∂μ₀` is not differentiable in `t`
(the norm has a corner at `0`), so the derivative-form Grönwall does not apply to it directly. The
antiderivative `U t = ∫₀ᵗ h`, however, *is* `C¹` with `U' = h`, and `U' = h ≤ K U`, `U 0 = 0` feed
the derivative-form `norm_le_gronwallBound_of_norm_deriv_right_le` to force `U ≡ 0`, whence
`h ≤ K U = 0`. -/

section UniquenessGronwall

open MeasureTheory Set
open scoped Topology

/-- **Integral-form Grönwall (nonnegative continuous functional).** If `h ≥ 0` is continuous on
`[0,T]` and `h t ≤ K · ∫₀ᵗ h` there, then `h ≡ 0` on `[0,T]`. Proved via the antiderivative
`U t = ∫₀ᵗ h`: `U` is `C¹` with `U' = h`, so `U' = h ≤ K U` and `U 0 = 0` give `U ≡ 0` by the
derivative-form Grönwall, whence `h t ≤ K U t = 0`. -/
theorem gronwall_integral_zero {K T : ℝ} (hT : 0 ≤ T) {h : ℝ → ℝ}
    (hcont : ContinuousOn h (Icc 0 T)) (hnonneg : ∀ t ∈ Icc 0 T, 0 ≤ h t)
    (hbound : ∀ t ∈ Icc 0 T, h t ≤ K * ∫ s in (0:ℝ)..t, h s) :
    ∀ t ∈ Icc 0 T, h t = 0 := by
  set U : ℝ → ℝ := fun t => ∫ s in (0:ℝ)..t, h s with hUdef
  have hInt : IntervalIntegrable h volume 0 T := hcont.intervalIntegrable_of_Icc hT
  have hIntOn : IntegrableOn h (Icc 0 T) volume := hcont.integrableOn_Icc
  have hUnonneg : ∀ t ∈ Icc 0 T, 0 ≤ U t := fun t ht =>
    intervalIntegral.integral_nonneg ht.1 (fun s hs => hnonneg s ⟨hs.1, hs.2.trans ht.2⟩)
  have hUcont : ContinuousOn U (Icc 0 T) := by
    have hc := intervalIntegral.continuousOn_primitive_interval
      (a := (0:ℝ)) (b := T) (μ := volume) (f := h) (by rw [Set.uIcc_of_le hT]; exact hIntOn)
    rwa [Set.uIcc_of_le hT] at hc
  have hUderiv : ∀ x ∈ Ico (0:ℝ) T, HasDerivWithinAt U (h x) (Ici x) x := by
    intro x hx
    have hxT : x ≤ T := hx.2.le
    have hmemFilter : Icc x T ∈ 𝓝[Ici x] x := by
      rw [← Set.Ici_inter_Iic]
      exact Filter.inter_mem self_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hx.2))
    have hIntx : IntervalIntegrable h volume 0 x :=
      hInt.mono_set (by rw [Set.uIcc_of_le hx.1, Set.uIcc_of_le hT]; exact Icc_subset_Icc le_rfl hxT)
    have hcwaIcc : ContinuousWithinAt h (Icc x T) x :=
      (hcont.mono (Icc_subset_Icc hx.1 le_rfl)).continuousWithinAt ⟨le_rfl, hxT⟩
    have hcwaIci : ContinuousWithinAt h (Ici x) x := hcwaIcc.mono_of_mem_nhdsWithin hmemFilter
    have hcwa : ContinuousWithinAt h (Ioi x) x := hcwaIci.mono Set.Ioi_subset_Ici_self
    have hmeasIci : StronglyMeasurableAtFilter h (𝓝[Ici x] x) volume :=
      ⟨Icc x T, hmemFilter, (hcont.mono (Icc_subset_Icc hx.1 le_rfl)).aestronglyMeasurable
        measurableSet_Icc⟩
    have hmeas : StronglyMeasurableAtFilter h (𝓝[Ioi x] x) volume :=
      hmeasIci.filter_mono (nhdsWithin_mono x Set.Ioi_subset_Ici_self)
    exact intervalIntegral.integral_hasDerivWithinAt_right hIntx hmeas hcwa
  have hUzero : ∀ t ∈ Icc 0 T, U t = 0 := by
    intro t ht
    have hb : ∀ x ∈ Ico (0:ℝ) T, ‖h x‖ ≤ K * ‖U x‖ + 0 := by
      intro x hx
      have hxIcc : x ∈ Icc (0:ℝ) T := ⟨hx.1, hx.2.le⟩
      rw [Real.norm_of_nonneg (hnonneg x hxIcc), Real.norm_of_nonneg (hUnonneg x hxIcc), add_zero]
      exact hbound x hxIcc
    have hU0 : ‖U 0‖ ≤ 0 := by simp [hUdef]
    have hg := norm_le_gronwallBound_of_norm_deriv_right_le hUcont hUderiv hU0 hb t ht
    rw [sub_zero, gronwallBound_ε0_δ0, Real.norm_of_nonneg (hUnonneg t ht)] at hg
    linarith [hUnonneg t ht]
  intro t ht
  have hbt : h t ≤ K * U t := hbound t ht
  rw [hUzero t ht, mul_zero] at hbt
  linarith [hnonneg t ht]

end UniquenessGronwall

/-! ### Velocity time-continuity and the FTC representation of the flow

The purely ODE-theoretic bridge that the mean-field uniqueness Grönwall consumes. Along a
mean-field flow `Φ` of a **sphere-supported probability** datum `μ₀`, the velocity
`s ↦ field((Φ_s)_#μ₀)(Φ_s x)` is continuous in time on `[0, duration]`. `IsMeanFieldFlow.deriv`
supplies only a pointwise `HasDerivAt`, so time-continuity is *derived*, not assumed: `s ↦ Φ_s x`
is continuous (a function with a derivative everywhere on the interval), `s ↦ (Φ_s)_#μ₀` is
`W₁`-continuous (dominated convergence through the coupling bound `W1_toReal_map_le_integral_norm`),
and `field` is jointly Lipschitz in `(point, W₁)` (`norm_field_sub_point_le`,
`norm_field_sub_measure_W1_le`). Continuity makes the velocity interval-integrable, so the
fundamental theorem of calculus represents the trajectory as
`Φ_t x - x = ∫₀ᵗ field((Φ_s)_#μ₀)(Φ_s x) ds` — the representation the Grönwall
(`gronwall_integral_zero`) consumes. -/

section FlowRepresentation

variable {p : AttnParams d} {μ₀ : Measure (Eucl d)} {Φ : ℝ → Eucl d → Eucl d}

/-- Each time slice of a mean-field flow pushes a probability datum to a probability measure. -/
theorem isProbabilityMeasure_map_flow [IsProbabilityMeasure μ₀] (hΦ : IsMeanFieldFlow p μ₀ Φ)
    {t : ℝ} (ht : t ∈ Set.Icc 0 p.duration) : IsProbabilityMeasure (μ₀.map (Φ t)) :=
  ⟨by rw [Measure.map_apply (hΦ.measurable t ht) MeasurableSet.univ, Set.preimage_univ];
      exact measure_univ⟩

/-- Each time slice keeps a sphere-supported datum sphere-supported (the sphere is invariant,
`sphere_bijOn`). -/
theorem map_flow_sphere_support [IsProbabilityMeasure μ₀] (hμ₀S : μ₀ (sphere d)ᶜ = 0)
    (hΦ : IsMeanFieldFlow p μ₀ Φ) {t : ℝ} (ht : t ∈ Set.Icc 0 p.duration) :
    (μ₀.map (Φ t)) (sphere d)ᶜ = 0 := by
  have hms : MeasurableSet ((sphere d)ᶜ) := Metric.isClosed_sphere.measurableSet.compl
  rw [Measure.map_apply (hΦ.measurable t ht) hms]
  refine measure_mono_null (fun y hy => ?_) hμ₀S
  simp only [Set.mem_preimage, Set.mem_compl_iff] at hy ⊢
  exact fun hyS => hy ((hΦ.sphere_bijOn t ht).mapsTo hyS)

/-- On the sphere, the pointwise displacement of two time slices is at most `2` (both slices land on
the sphere), the dominating bound for the dominated-convergence arguments below. -/
theorem norm_flow_sub_le_two (hΦ : IsMeanFieldFlow p μ₀ Φ) {s t : ℝ}
    (hs : s ∈ Set.Icc 0 p.duration) (ht : t ∈ Set.Icc 0 p.duration) {y : Eucl d}
    (hy : y ∈ sphere d) : ‖Φ s y - Φ t y‖ ≤ 2 := by
  have h1 : Φ s y ∈ sphere d := (hΦ.sphere_bijOn s hs).mapsTo hy
  have h2 : Φ t y ∈ sphere d := (hΦ.sphere_bijOn t ht).mapsTo hy
  calc ‖Φ s y - Φ t y‖ ≤ ‖Φ s y‖ + ‖Φ t y‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_eq_one_of_mem_sphere h1, norm_eq_one_of_mem_sphere h2]; norm_num

/-- The `μ₀`-average displacement between two time slices is integrable (bounded by `2`). -/
theorem integrable_norm_flow_sub [IsProbabilityMeasure μ₀] (hμ₀S : μ₀ (sphere d)ᶜ = 0)
    (hΦ : IsMeanFieldFlow p μ₀ Φ) {s t : ℝ} (hs : s ∈ Set.Icc 0 p.duration)
    (ht : t ∈ Set.Icc 0 p.duration) : Integrable (fun y => ‖Φ s y - Φ t y‖) μ₀ := by
  refine Integrable.mono' (integrable_const (2 : ℝ))
    ((hΦ.measurable s hs).sub (hΦ.measurable t ht)).norm.aestronglyMeasurable ?_
  refine ae_of_sphere_supported hμ₀S (fun y hy => ?_)
  rw [norm_norm]; exact norm_flow_sub_le_two hΦ hs ht hy

/-- The `μ₀`-average flow displacement `∫ ‖Φ_s − Φ_{s₀}‖ ∂μ₀ → 0` as `s → s₀` (dominated
convergence: pointwise on the sphere each `s ↦ Φ_s y` is continuous, dominated by `2`). -/
theorem integral_flow_sub_tendsto_zero [IsProbabilityMeasure μ₀] (hμ₀S : μ₀ (sphere d)ᶜ = 0)
    (hΦ : IsMeanFieldFlow p μ₀ Φ) {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Icc 0 p.duration) :
    Filter.Tendsto (fun s => ∫ y, ‖Φ s y - Φ s₀ y‖ ∂μ₀)
      (nhdsWithin s₀ (Set.Icc 0 p.duration)) (nhds 0) := by
  have hcont : ContinuousWithinAt (fun s => ∫ y, ‖Φ s y - Φ s₀ y‖ ∂μ₀)
      (Set.Icc 0 p.duration) s₀ := by
    refine MeasureTheory.continuousWithinAt_of_dominated (bound := fun _ => (2 : ℝ)) ?_ ?_
      (integrable_const _) ?_
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact ((hΦ.measurable s hs).sub (hΦ.measurable s₀ hs₀)).norm.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with s hs
      refine ae_of_sphere_supported hμ₀S (fun y hy => ?_)
      rw [norm_norm]; exact norm_flow_sub_le_two hΦ hs hs₀ hy
    · refine ae_of_sphere_supported hμ₀S (fun y hy => ?_)
      exact ((((hΦ.deriv y hy s₀ hs₀).continuousAt).continuousWithinAt).sub
        continuousWithinAt_const).norm
  have hval : Filter.Tendsto (fun s => ∫ y, ‖Φ s y - Φ s₀ y‖ ∂μ₀)
      (nhdsWithin s₀ (Set.Icc 0 p.duration)) (nhds (∫ y, ‖Φ s₀ y - Φ s₀ y‖ ∂μ₀)) := hcont
  simpa using hval

/-- **Leaf A — velocity time-continuity.** Along a mean-field flow of a sphere-supported
probability datum, the velocity `s ↦ field((Φ_s)_#μ₀)(Φ_s x)` is continuous on `[0, duration]`. -/
theorem velocity_continuousOn [IsProbabilityMeasure μ₀] (hμ₀S : μ₀ (sphere d)ᶜ = 0)
    (hΦ : IsMeanFieldFlow p μ₀ Φ) {x : Eucl d} (hx : x ∈ sphere d) :
    ContinuousOn (fun s => p.field (μ₀.map (Φ s)) (Φ s x)) (Set.Icc 0 p.duration) := by
  intro s₀ hs₀
  set Cp : ℝ := (‖p.V‖ * (2 * ‖p.B‖ * Real.exp (4 * ‖p.B‖)) + ‖p.W‖ * ‖p.U‖)
    + 2 * (‖p.V‖ * Real.exp (2 * ‖p.B‖) + ‖p.W‖ * (‖p.U‖ + ‖p.b‖)) with hCp
  set Cm : ℝ := ‖p.V‖ * ((Real.exp (2 * ‖p.B‖) + Real.exp (4 * ‖p.B‖)) * (1 + ‖p.B‖)) with hCm
  have hCm0 : 0 ≤ Cm := by rw [hCm]; positivity
  -- The two scalar quantities that vanish at `s₀`.
  have ha : Filter.Tendsto (fun s => ‖Φ s x - Φ s₀ x‖)
      (nhdsWithin s₀ (Set.Icc 0 p.duration)) (nhds 0) := by
    have hnorm : ContinuousWithinAt (fun s => ‖Φ s x - Φ s₀ x‖) (Set.Icc 0 p.duration) s₀ :=
      ((((hΦ.deriv x hx s₀ hs₀).continuousAt).continuousWithinAt).sub continuousWithinAt_const).norm
    have hval : Filter.Tendsto (fun s => ‖Φ s x - Φ s₀ x‖)
        (nhdsWithin s₀ (Set.Icc 0 p.duration)) (nhds ‖Φ s₀ x - Φ s₀ x‖) := hnorm
    simpa using hval
  have hb := integral_flow_sub_tendsto_zero hμ₀S hΦ hs₀
  have hg : Filter.Tendsto
      (fun s => Cp * ‖Φ s x - Φ s₀ x‖ + Cm * ∫ y, ‖Φ s y - Φ s₀ y‖ ∂μ₀)
      (nhdsWithin s₀ (Set.Icc 0 p.duration)) (nhds 0) := by
    have := (Filter.Tendsto.const_mul Cp ha).add (Filter.Tendsto.const_mul Cm hb)
    simpa using this
  -- Squeeze the field difference by `Cp·a + Cm·b`.
  have key : Filter.Tendsto
      (fun s => p.field (μ₀.map (Φ s)) (Φ s x) - p.field (μ₀.map (Φ s₀)) (Φ s₀ x))
      (nhdsWithin s₀ (Set.Icc 0 p.duration)) (nhds 0) := by
    refine squeeze_zero_norm' ?_ hg
    filter_upwards [self_mem_nhdsWithin] with s hs
    haveI := isProbabilityMeasure_map_flow hΦ hs
    haveI := isProbabilityMeasure_map_flow hΦ hs₀
    have hνsS := map_flow_sphere_support hμ₀S hΦ hs
    have hνs₀S := map_flow_sphere_support hμ₀S hΦ hs₀
    have hxs : Φ s x ∈ sphere d := (hΦ.sphere_bijOn s hs).mapsTo hx
    have hxs₀ : Φ s₀ x ∈ sphere d := (hΦ.sphere_bijOn s₀ hs₀).mapsTo hx
    have hW1ne : W1 (μ₀.map (Φ s)) (μ₀.map (Φ s₀)) ≠ ⊤ :=
      W1_ne_top_of_sphere_supported _ _ hνsS hνs₀S
    -- Point modulus at the measure `(Φ_s)_#μ₀`.
    have hpt : ‖p.field (μ₀.map (Φ s)) (Φ s x) - p.field (μ₀.map (Φ s)) (Φ s₀ x)‖
        ≤ Cp * ‖Φ s x - Φ s₀ x‖ := by
      have := norm_field_sub_point_le p (μ₀.map (Φ s)) hνsS hxs hxs₀
      rwa [← hCp] at this
    -- Measure modulus, then the coupling bound.
    have hms : ‖p.field (μ₀.map (Φ s)) (Φ s₀ x) - p.field (μ₀.map (Φ s₀)) (Φ s₀ x)‖
        ≤ Cm * ∫ y, ‖Φ s y - Φ s₀ y‖ ∂μ₀ := by
      have hmod := norm_field_sub_measure_W1_le p hνsS hνs₀S hW1ne hxs₀
      rw [← hCm] at hmod
      have hcoup : (W1 (μ₀.map (Φ s)) (μ₀.map (Φ s₀))).toReal ≤ ∫ y, ‖Φ s y - Φ s₀ y‖ ∂μ₀ :=
        W1_toReal_map_le_integral_norm (hΦ.measurable s hs) (hΦ.measurable s₀ hs₀)
          (integrable_norm_flow_sub hμ₀S hΦ hs hs₀)
      exact hmod.trans (mul_le_mul_of_nonneg_left hcoup hCm0)
    have hsplit :
        p.field (μ₀.map (Φ s)) (Φ s x) - p.field (μ₀.map (Φ s₀)) (Φ s₀ x)
          = (p.field (μ₀.map (Φ s)) (Φ s x) - p.field (μ₀.map (Φ s)) (Φ s₀ x))
            + (p.field (μ₀.map (Φ s)) (Φ s₀ x) - p.field (μ₀.map (Φ s₀)) (Φ s₀ x)) :=
      (sub_add_sub_cancel _ _ _).symm
    calc ‖p.field (μ₀.map (Φ s)) (Φ s x) - p.field (μ₀.map (Φ s₀)) (Φ s₀ x)‖
        = ‖(p.field (μ₀.map (Φ s)) (Φ s x) - p.field (μ₀.map (Φ s)) (Φ s₀ x))
            + (p.field (μ₀.map (Φ s)) (Φ s₀ x) - p.field (μ₀.map (Φ s₀)) (Φ s₀ x))‖ := by
          rw [hsplit]
      _ ≤ ‖p.field (μ₀.map (Φ s)) (Φ s x) - p.field (μ₀.map (Φ s)) (Φ s₀ x)‖
            + ‖p.field (μ₀.map (Φ s)) (Φ s₀ x) - p.field (μ₀.map (Φ s₀)) (Φ s₀ x)‖ :=
          norm_add_le _ _
      _ ≤ Cp * ‖Φ s x - Φ s₀ x‖ + Cm * ∫ y, ‖Φ s y - Φ s₀ y‖ ∂μ₀ := add_le_add hpt hms
  rwa [tendsto_sub_nhds_zero_iff] at key

/-- **Leaf B — FTC representation of the flow.** The trajectory of a sphere point along a mean-field
flow of a sphere-supported probability datum is the time integral of its velocity:
`Φ_t x - x = ∫₀ᵗ field((Φ_s)_#μ₀)(Φ_s x) ds`. This is the representation the uniqueness Grönwall
(`gronwall_integral_zero`) consumes. -/
theorem flow_sub_eq_integral_field [IsProbabilityMeasure μ₀] (hμ₀S : μ₀ (sphere d)ᶜ = 0)
    (hΦ : IsMeanFieldFlow p μ₀ Φ) {x : Eucl d} (hx : x ∈ sphere d)
    {t : ℝ} (ht : t ∈ Set.Icc 0 p.duration) :
    Φ t x - x = ∫ s in (0)..t, p.field (μ₀.map (Φ s)) (Φ s x) := by
  have h0mem : (0 : ℝ) ∈ Set.Icc 0 p.duration := ⟨le_refl 0, p.duration_nonneg⟩
  have hsub : Set.uIcc 0 t ⊆ Set.Icc 0 p.duration := Set.uIcc_subset_Icc h0mem ht
  have hderiv : ∀ s ∈ Set.uIcc 0 t,
      HasDerivAt (fun s => Φ s x) (p.field (μ₀.map (Φ s)) (Φ s x)) s :=
    fun s hs => hΦ.deriv x hx s (hsub hs)
  have hint : IntervalIntegrable (fun s => p.field (μ₀.map (Φ s)) (Φ s x)) volume 0 t :=
    ((velocity_continuousOn hμ₀S hΦ hx).mono hsub).intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hftc, hΦ.init]; simp

end FlowRepresentation

/-! ### The averaged Grönwall inequality

Averaging the pointwise field bound over the sphere-supported probability datum `μ₀` turns the two
flows' distance functional `meanFlowDist μ₀ Φ Ψ t = ∫ ‖Φ_t x − Ψ_t x‖ ∂μ₀` into the integral-Grönwall
hypothesis `h t ≤ K ∫₀ᵗ h`. The FTC representation (`flow_sub_eq_integral_field`) writes the pointwise
displacement as a time integral of the field difference; the joint `(point, W₁)` modulus bounds that
difference by `Cp‖Φ_s x − Ψ_s x‖ + Cm·(W₁((Φ_s)_#μ₀, (Ψ_s)_#μ₀)).toReal`; a Fubini/Tonelli swap
integrates it over `μ₀`, and the coupling bound `W1_toReal_map_le_integral_norm` controls the `W₁`
term by `meanFlowDist s` itself — collapsing the bound to `K·meanFlowDist s` with `K = Cp + Cm`. -/

section AveragedGronwall

open MeasureTheory

variable {p : AttnParams d} {μ₀ : Measure (Eucl d)} {Φ Ψ : ℝ → Eucl d → Eucl d}

/-- The `μ₀`-averaged distance between two mean-field flow slices at time `t`. This is the functional
the mean-field uniqueness Grönwall drives to zero. -/
noncomputable def meanFlowDist (μ₀ : Measure (Eucl d)) (Φ Ψ : ℝ → Eucl d → Eucl d) (t : ℝ) : ℝ :=
  ∫ x, ‖Φ t x - Ψ t x‖ ∂μ₀

theorem meanFlowDist_nonneg (t : ℝ) : 0 ≤ meanFlowDist μ₀ Φ Ψ t :=
  integral_nonneg fun _ => norm_nonneg _

/-- The averaged flow distance is continuous in time on `[0, duration]` (dominated convergence: each
`t ↦ ‖Φ_t x − Ψ_t x‖` is continuous on the sphere and dominated by `2`). -/
theorem meanFlowDist_continuousOn [IsProbabilityMeasure μ₀] (hμ₀S : μ₀ (sphere d)ᶜ = 0)
    (hΦ : IsMeanFieldFlow p μ₀ Φ) (hΨ : IsMeanFieldFlow p μ₀ Ψ) :
    ContinuousOn (meanFlowDist μ₀ Φ Ψ) (Set.Icc 0 p.duration) := by
  intro t₀ ht₀
  refine continuousWithinAt_of_dominated (bound := fun _ => (2 : ℝ)) ?_ ?_
    (integrable_const _) ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact ((hΦ.measurable t ht).sub (hΨ.measurable t ht)).norm.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with t ht
    refine ae_of_sphere_supported hμ₀S (fun x hx => ?_)
    rw [norm_norm]
    have h1 : Φ t x ∈ sphere d := (hΦ.sphere_bijOn t ht).mapsTo hx
    have h2 : Ψ t x ∈ sphere d := (hΨ.sphere_bijOn t ht).mapsTo hx
    calc ‖Φ t x - Ψ t x‖ ≤ ‖Φ t x‖ + ‖Ψ t x‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_eq_one_of_mem_sphere h1, norm_eq_one_of_mem_sphere h2]; norm_num
  · refine ae_of_sphere_supported hμ₀S (fun x hx => ?_)
    exact ((((hΦ.deriv x hx t₀ ht₀).continuousAt).continuousWithinAt).sub
      (((hΨ.deriv x hx t₀ ht₀).continuousAt).continuousWithinAt)).norm

end AveragedGronwall

end MeasureToMeasure.Foundations
