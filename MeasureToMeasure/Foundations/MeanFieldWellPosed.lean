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

end MeasureToMeasure.Foundations
