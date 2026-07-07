import MeasureToMeasure.Foundations.WassersteinFinite

/-!
# `W₁ ≤ 2·TV` on the sphere via the min-coupling (M3b existence, leaf S3b-iii)

Toward the hard direction of the `W₁ ↔ weak` comparison (leaf S3b, `exists_meanFieldFlow`): the
Wasserstein-1 distance between two sphere-supported probability measures is controlled by their total
variation. This is the analytic heart of the discrete-discrepancy step — with `μ, ν` the cell-rounded
pushforwards of two nearby measures, `2·TV` is `diam · ∑ₖ |μ(Aₖ) − ν(Aₖ)|`, which portmanteau drives
to `0`.

* `W1_le_two_mul_tv` — `W₁(μ, ν) ≤ 2 · (μ − μ ⊓ ν)(univ)` for sphere-supported probability measures.
  The mass `(μ − μ ⊓ ν)(univ) = 1 − (μ ⊓ ν)(univ)` is the total variation. Proof by the **min-coupling**:
  keep the shared mass `μ ⊓ ν` on the diagonal (zero cost) and move the residual mass
  `δ = (μ − μ⊓ν)(univ)` via a product coupling of the *normalised* residuals `δ⁻¹(μ − μ⊓ν)`,
  `δ⁻¹(ν − μ⊓ν)`. These are probability measures because both residuals have the same mass `δ`
  (both `= 1 − (μ⊓ν)(univ)`, as `μ, ν` are probabilities), and they are sphere-supported, so
  `edist ≤ 2` a.e. — the product coupling costs `≤ 2·δ`.

Mathlib has no optimal transport, so this is proved from the repo's bespoke `W₁`/`IsCoupling` layer.

M3b staging: consumed when `exists_meanFieldFlow` is discharged; see RESEARCH.md.
-/

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace MeasureToMeasure

variable {d : ℕ}

/-- **`W₁` is controlled by total variation on the sphere.** For sphere-supported probability measures,
`W₁(μ, ν) ≤ 2 · (μ − μ ⊓ ν)(univ)`, the diameter `2` times the total-variation mass. The min-coupling:
shared mass `μ ⊓ ν` sits on the diagonal (zero cost), the residual mass `δ` is moved by a product
coupling of the normalised residuals (`edist ≤ 2` a.e. — both are sphere-supported). -/
theorem W1_le_two_mul_tv {μ ν : Measure (Eucl d)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ (sphere d)ᶜ = 0) (hν : ν (sphere d)ᶜ = 0) :
    W1 μ ν ≤ 2 * ((μ - μ ⊓ ν) Set.univ) := by
  set ρ : Measure (Eucl d) := μ ⊓ ν with hρ
  have hρμ : ρ ≤ μ := by rw [hρ]; exact inf_le_left
  have hρν : ρ ≤ ν := by rw [hρ]; exact inf_le_right
  haveI hρfin : IsFiniteMeasure ρ := isFiniteMeasure_of_le μ hρμ
  have hμu : μ Set.univ = 1 := measure_univ
  have hνu : ν Set.univ = 1 := measure_univ
  -- The two residual masses coincide (both `= 1 − ρ(univ)`).
  have hmasses : (μ - ρ) Set.univ = (ν - ρ) Set.univ := by
    rw [Measure.sub_apply MeasurableSet.univ hρμ, Measure.sub_apply MeasurableSet.univ hρν, hμu, hνu]
  set δ : ℝ≥0∞ := (μ - ρ) Set.univ with hδ
  have hres : (ν - ρ) Set.univ = δ := hmasses.symm
  have hδ_le : δ ≤ μ Set.univ := by rw [hδ]; exact Measure.le_iff'.1 Measure.sub_le Set.univ
  have hδ_ne_top : δ ≠ ⊤ := ne_top_of_le_ne_top (measure_ne_top μ Set.univ) hδ_le
  rcases eq_or_ne δ 0 with hδ0 | hδ0
  · -- Degenerate case `δ = 0`: `μ = ρ = ν`, so `W₁ μ ν = 0`.
    have hμ0 : (μ - ρ) Set.univ = 0 := hδ.symm.trans hδ0
    have hν0 : (ν - ρ) Set.univ = 0 := hres.trans hδ0
    have hμρ : μ = ρ := by
      have h := Measure.sub_add_cancel_of_le hρμ
      rw [Measure.measure_univ_eq_zero.1 hμ0, zero_add] at h
      exact h.symm
    have hνρ : ν = ρ := by
      have h := Measure.sub_add_cancel_of_le hρν
      rw [Measure.measure_univ_eq_zero.1 hν0, zero_add] at h
      exact h.symm
    rw [hμρ.trans hνρ.symm, W1_self_eq_zero]
    exact zero_le
  · -- Main case `δ > 0`: build the min-coupling.
    set P : Measure (Eucl d) := δ⁻¹ • (μ - ρ) with hP
    set Q : Measure (Eucl d) := δ⁻¹ • (ν - ρ) with hQ
    haveI hPprob : IsProbabilityMeasure P := by
      refine ⟨?_⟩
      rw [hP, Measure.smul_apply, smul_eq_mul, ← hδ, ENNReal.inv_mul_cancel hδ0 hδ_ne_top]
    haveI hQprob : IsProbabilityMeasure Q := by
      refine ⟨?_⟩
      rw [hQ, Measure.smul_apply, smul_eq_mul, hres, ENNReal.inv_mul_cancel hδ0 hδ_ne_top]
    have hPsupp : P (sphere d)ᶜ = 0 := by
      rw [hP, Measure.smul_apply, smul_eq_mul]
      have h0 : (μ - ρ) (sphere d)ᶜ = 0 :=
        le_zero_iff.1 ((Measure.le_iff'.1 Measure.sub_le _).trans_eq hμ)
      rw [h0, mul_zero]
    have hQsupp : Q (sphere d)ᶜ = 0 := by
      rw [hQ, Measure.smul_apply, smul_eq_mul]
      have h0 : (ν - ρ) (sphere d)ᶜ = 0 :=
        le_zero_iff.1 ((Measure.le_iff'.1 Measure.sub_le _).trans_eq hν)
      rw [h0, mul_zero]
    -- The product coupling of the residuals costs `≤ 2` (both sphere-supported).
    have hcost : ∫⁻ p, edist p.1 p.2 ∂(P.prod Q) ≤ 2 := by
      have hae : ∀ᵐ p ∂(P.prod Q), edist p.1 p.2 ≤ 2 := by
        have h1 : ∀ᵐ p ∂(P.prod Q), ‖p.1‖ ≤ 1 :=
          Measure.quasiMeasurePreserving_fst.ae (ae_norm_le_one_of_sphere_supported hPsupp)
        have h2 : ∀ᵐ p ∂(P.prod Q), ‖p.2‖ ≤ 1 :=
          Measure.quasiMeasurePreserving_snd.ae (ae_norm_le_one_of_sphere_supported hQsupp)
        filter_upwards [h1, h2] with p hp1 hp2
        have hdist : dist p.1 p.2 ≤ 2 := by
          rw [dist_eq_norm]
          calc ‖p.1 - p.2‖ ≤ ‖p.1‖ + ‖p.2‖ := norm_sub_le _ _
            _ ≤ 2 := by linarith
        rw [edist_dist]
        calc ENNReal.ofReal (dist p.1 p.2) ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hdist
          _ = 2 := by rw [ENNReal.ofReal_ofNat]
      calc ∫⁻ p, edist p.1 p.2 ∂(P.prod Q)
          ≤ ∫⁻ _, (2 : ℝ≥0∞) ∂(P.prod Q) := lintegral_mono_ae hae
        _ = 2 := by rw [lintegral_const, measure_univ, mul_one]
    -- Marginals of the `δ`-scaled product coupling.
    have hsub : (δ • (P.prod Q)).fst = δ • P := by
      calc (δ • (P.prod Q)).fst = δ • (P.prod Q).fst := Measure.map_smul δ (P.prod Q) Prod.fst
        _ = δ • P := by rw [Measure.fst_prod]
    have hsub' : (δ • (P.prod Q)).snd = δ • Q := by
      calc (δ • (P.prod Q)).snd = δ • (P.prod Q).snd := Measure.map_smul δ (P.prod Q) Prod.snd
        _ = δ • Q := by rw [Measure.snd_prod]
    -- The min-coupling `γ = diag_#ρ + δ·(P⊗Q)` couples `μ` and `ν`.
    have hfst : (ρ.map (fun x => (x, x)) + δ • (P.prod Q)).fst = μ := by
      rw [Measure.fst_add, (isCoupling_diagonal ρ).1, hsub, hP, smul_smul,
        ENNReal.mul_inv_cancel hδ0 hδ_ne_top, one_smul, add_comm]
      exact Measure.sub_add_cancel_of_le hρμ
    have hsnd : (ρ.map (fun x => (x, x)) + δ • (P.prod Q)).snd = ν := by
      rw [Measure.snd_add, (isCoupling_diagonal ρ).2, hsub', hQ, smul_smul,
        ENNReal.mul_inv_cancel hδ0 hδ_ne_top, one_smul, add_comm]
      exact Measure.sub_add_cancel_of_le hρν
    have hcpl : IsCoupling (ρ.map (fun x => (x, x)) + δ • (P.prod Q)) μ ν := ⟨hfst, hsnd⟩
    -- Total cost: diagonal part is free, product part costs `≤ 2·δ`.
    have hcostγ : transportCost (ρ.map (fun x => (x, x)) + δ • (P.prod Q)) ≤ 2 * δ := by
      rw [transportCost, lintegral_add_measure]
      have hdiag : ∫⁻ p, edist p.1 p.2 ∂(ρ.map (fun x => (x, x))) = 0 := transportCost_diagonal ρ
      rw [hdiag, zero_add, lintegral_smul_measure, smul_eq_mul]
      calc δ * ∫⁻ p, edist p.1 p.2 ∂(P.prod Q) ≤ δ * 2 := by gcongr
        _ = 2 * δ := mul_comm δ 2
    calc W1 μ ν ≤ transportCost (ρ.map (fun x => (x, x)) + δ • (P.prod Q)) := W1_le_transportCost hcpl
      _ ≤ 2 * δ := hcostγ

end MeasureToMeasure
