import MeasureToMeasure.Foundations.Wasserstein
import MeasureToMeasure.Foundations.GeodesicDistance
import MeasureToMeasure.Foundations.SphereMeasureBridge

/-!
# Two discrete measures on the same points are `W₂`-close when their weights are close

The paper's Section 2 Step 1 posits, without construction or proof, a partition of each connected
piece into `M` sub-pieces of EXACT prescribed mass, each containing its own target point in its
interior. Read directly (App./Section 2, pp. 12-14): this is a genuine unproven existence claim,
mathematically equivalent to a substantial semi-discrete optimal-transport theorem (weighted
Voronoi / power-diagram existence, Aurenhammer-Hoffmann-Aronov 1998) -- realistically its own
sub-campaign, not a fixable proof-engineering deviation like the other paper-construction gaps
found this session.

This leaf builds the tool that sidesteps that existence theorem, using the `ε` slack `prop_2_2`
already carries in its own conclusion (`W2(...) ≤ ε`, not exact equality): exact per-piece mass was
never actually required, only that a mass discrepancy be small enough to be absorbed into the SAME
`ε`, via the triangle inequality `W2(Σβₖ•Pₖ, Σαₖ•δₓₖ) ≤ W2(Σβₖ•Pₖ, Σβₖ•δₓₖ) + W2(Σβₖ•δₓₖ, Σαₖ•δₓₖ)`.
The first term is `gated_forest_to_target_retention` + `W2_dirac_le_of_geodesicBall_mass`'s job
(mass concentrated near a target is close to its Dirac); this leaf is the second term, bounding two
discrete measures on the SAME support points with DIFFERENT weights.

**The construction.** The coupling that matches as much mass as possible on the diagonal (zero
cost) and transports only the residual: `γₖ := min(αₖ,βₖ)` is matched exactly at `xₖ`; the leftover
"excess" (`βₖ-γₖ`, where `β` exceeds `α`) and "deficit" (`αₖ-γₖ`, where `α` exceeds `β`) have EQUAL
total mass `r := Σ(βₖ-γₖ) = Σ(αₖ-γₖ)` (since both weight vectors sum to 1), and are coupled via the
normalized product `r⁻¹•(A.prod B)` -- the unique coupling of two measures of the same total mass
`r`. Its cost is bounded by the sphere's own diameter squared (4) times `r`, giving the final bound
`W₂ ≤ 2√r`.

M3b/mid-level staging: the reframed Stage 1 of the `prop_2_2` Steps 2-3 campaign (ball packing,
path chaining, and this weight-discrepancy bound); see the `prop-2-2-steps-2-3-campaign` project
notes. Combining this with a greedy Besicovitch-packing assignment (approximate rather than exact
per-piece mass) is the next step, not yet built.
-/

namespace MeasureToMeasure

open MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- A mixture (sum) of couplings is a coupling of the sums -- the 2-term additive case, simpler
than routing through `isCoupling_finset_sum_smul`'s `Fin M`-indexed mixture machinery. -/
theorem isCoupling_add {π1 π2 : Measure (Eucl d × Eucl d)} {P1 P2 Q1 Q2 : Measure (Eucl d)}
    (h1 : IsCoupling π1 P1 Q1) (h2 : IsCoupling π2 P2 Q2) :
    IsCoupling (π1 + π2) (P1 + P2) (Q1 + Q2) := by
  constructor
  · show Measure.map Prod.fst (π1 + π2) = P1 + P2
    rw [Measure.map_add π1 π2 measurable_fst]
    show π1.fst + π2.fst = P1 + P2
    rw [h1.1, h2.1]
  · show Measure.map Prod.snd (π1 + π2) = Q1 + Q2
    rw [Measure.map_add π1 π2 measurable_snd]
    show π1.snd + π2.snd = Q1 + Q2
    rw [h1.2, h2.2]

/-- The squared transport cost is additive over a 2-term sum of couplings. -/
theorem sqTransportCost_add (π1 π2 : Measure (Eucl d × Eucl d)) :
    sqTransportCost (π1 + π2) = sqTransportCost π1 + sqTransportCost π2 := by
  rw [sqTransportCost, sqTransportCost, sqTransportCost, lintegral_add_measure]

/-- The **normalized product** of two measures of the SAME total mass `r` is a coupling of them --
the unique coupling when both sides have equal, non-probability total mass (generalizes
`isCoupling_prod`, which needs both factors to already be probability measures). -/
theorem isCoupling_scaled_prod {A B : Measure (Eucl d)} [SFinite A] [SFinite B] {r : ℝ≥0∞}
    (hr0 : r ≠ 0) (hrtop : r ≠ ⊤) (hA : A Set.univ = r) (hB : B Set.univ = r) :
    IsCoupling (r⁻¹ • (A.prod B)) A B := by
  constructor
  · show Measure.map Prod.fst (r⁻¹ • (A.prod B)) = A
    rw [Measure.map_smul, Measure.map_fst_prod, hB, smul_smul,
      ENNReal.inv_mul_cancel hr0 hrtop, one_smul]
  · show Measure.map Prod.snd (r⁻¹ • (A.prod B)) = B
    rw [Measure.map_smul, Measure.map_snd_prod, hA, smul_smul,
      ENNReal.inv_mul_cancel hr0 hrtop, one_smul]

/-- **Two sphere-supported measures of total mass `r` couple with squared cost `≤4r`** -- the
sphere's own diameter (2) squared, times the shared total mass. -/
theorem sqTransportCost_scaled_prod_le {A B : Measure (Eucl d)} [SFinite A] [SFinite B]
    (hAS : A (sphere d)ᶜ = 0) (hBS : B (sphere d)ᶜ = 0) {r : ℝ≥0∞} (hr0 : r ≠ 0) (hrtop : r ≠ ⊤)
    (hA : A Set.univ = r) (hB : B Set.univ = r) :
    sqTransportCost (r⁻¹ • (A.prod B)) ≤ 4 * r := by
  rw [sqTransportCost, lintegral_smul_measure]
  have haeA : ∀ᵐ x ∂A, x ∈ sphere d := by rw [ae_iff]; exact hAS
  have haeB : ∀ᵐ y ∂B, y ∈ sphere d := by rw [ae_iff]; exact hBS
  have haeprod : ∀ᵐ p ∂(A.prod B), p.1 ∈ sphere d ∧ p.2 ∈ sphere d :=
    (Measure.ae_prod_iff_ae_ae
      (((measurableSet_sphere d).preimage measurable_fst).inter
        ((measurableSet_sphere d).preimage measurable_snd))).mpr
      (haeA.mono fun x hx => haeB.mono fun y hy => ⟨hx, hy⟩)
  have hptbound : ∀ᵐ p ∂(A.prod B), edist p.1 p.2 ^ 2 ≤ (4 : ℝ≥0∞) := by
    filter_upwards [haeprod] with p hp
    have hedist : edist p.1 p.2 = ENNReal.ofReal ‖p.1 - p.2‖ := by rw [edist_dist, dist_eq_norm]
    rw [hedist]
    have hdiam : ‖p.1 - p.2‖ ≤ 2 := by
      have h1n : ‖p.1‖ = 1 := norm_eq_one_of_mem_sphere hp.1
      have h2n : ‖p.2‖ = 1 := norm_eq_one_of_mem_sphere hp.2
      calc ‖p.1 - p.2‖ ≤ ‖p.1‖ + ‖p.2‖ := norm_sub_le _ _
        _ = 2 := by rw [h1n, h2n]; ring
    calc (ENNReal.ofReal ‖p.1 - p.2‖) ^ 2 ≤ (ENNReal.ofReal (2:ℝ)) ^ 2 := by gcongr
      _ = 4 := by rw [← ENNReal.ofReal_pow (by norm_num)]; norm_num
  have hstep1 : ∫⁻ p, edist p.1 p.2 ^ 2 ∂(A.prod B) ≤ ∫⁻ _p, (4 : ℝ≥0∞) ∂(A.prod B) :=
    lintegral_mono_ae hptbound
  have hstep2 : (∫⁻ _p : Eucl d × Eucl d, (4 : ℝ≥0∞) ∂(A.prod B)) = 4 * (A Set.univ * B Set.univ) := by
    rw [lintegral_const, ← Set.univ_prod_univ, Measure.prod_prod]
  have hstep3 : 4 * (A Set.univ * B Set.univ) = 4 * (r * r) := by
    rw [hA, hB]
  have hcost : ∫⁻ p, edist p.1 p.2 ^ 2 ∂(A.prod B) ≤ 4 * (r * r) := by
    rw [← hstep3, ← hstep2]
    exact hstep1
  calc r⁻¹ * ∫⁻ p, edist p.1 p.2 ^ 2 ∂(A.prod B) ≤ r⁻¹ * (4 * (r * r)) := by gcongr
    _ = 4 * (r⁻¹ * r * r) := by ring
    _ = 4 * (1 * r) := by rw [ENNReal.inv_mul_cancel hr0 hrtop]
    _ = 4 * r := by rw [one_mul]

/-- Finset-sum version of ENNReal truncated subtraction distributing over a sum, given the
subtrahend is pointwise below the minuend (needed since ENNReal is not cancellative, so the
general-ordered-monoid `Finset.sum_tsub_distrib` doesn't apply). -/
theorem Finset.sum_tsub_of_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (f g : ι → ℝ≥0∞)
    (hgtop : ∀ i ∈ s, g i ≠ ⊤) (hfg : ∀ i ∈ s, g i ≤ f i) :
    ∑ i ∈ s, (f i - g i) = ∑ i ∈ s, f i - ∑ i ∈ s, g i := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s' ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha,
      ih (fun i hi => hgtop i (Finset.mem_insert_of_mem hi))
        (fun i hi => hfg i (Finset.mem_insert_of_mem hi))]
    have hga : g a ≤ f a := hfg a (Finset.mem_insert_self a s')
    have hgatop : g a ≠ ⊤ := hgtop a (Finset.mem_insert_self a s')
    have hgstop : ∑ i ∈ s', g i ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr (fun i hi => hgtop i (Finset.mem_insert_of_mem hi))
    have hgs : ∑ i ∈ s', g i ≤ ∑ i ∈ s', f i :=
      Finset.sum_le_sum (fun i hi => hfg i (Finset.mem_insert_of_mem hi))
    exact (ENNReal.cancel_of_ne hgatop).tsub_add_tsub_comm (ENNReal.cancel_of_ne hgstop) hga hgs

theorem sum_smul_dirac_univ {M : ℕ} (x : Fin M → Eucl d) (c : Fin M → ℝ≥0∞) :
    (∑ k, c k • Measure.dirac (x k)) Set.univ = ∑ k, c k := by
  simp [Measure.finsetSum_apply, Measure.smul_apply]

theorem sFinite_sum_smul_dirac {M : ℕ} (x : Fin M → Eucl d) (c : Fin M → ℝ≥0∞) :
    SFinite (∑ k, c k • Measure.dirac (x k)) := by
  apply Finset.sum_induction _ (fun μ => SFinite μ)
  · intro a b _ _; infer_instance
  · infer_instance
  · intro k _; infer_instance

/-- **Two discrete measures on the same points, different weights, are `W₂`-close when the
weights are close.** Absorbs the discrepancy `Σ(βₖ-min(αₖ,βₖ))` (half the total-variation distance
between the weight vectors) into a `W₂` bound via the coupling that matches as much mass as
possible on the diagonal and transports the residual (equal-sized excess/deficit) at cost bounded
by the sphere's own diameter. -/
theorem W2_diracSum_le_of_weight_diff {M : ℕ} (x : Fin M → Eucl d) (hx : ∀ k, x k ∈ sphere d)
    (α β : Fin M → ℝ≥0∞) (hα : ∑ k, α k = 1) (hβ : ∑ k, β k = 1) :
    W2 (∑ k, β k • Measure.dirac (x k)) (∑ k, α k • Measure.dirac (x k)) ≤
      2 * (∑ k, (β k - min (α k) (β k))) ^ (2⁻¹ : ℝ) := by
  set r := ∑ k, (β k - min (α k) (β k)) with hr_def
  have hβtop : ∀ k : Fin M, β k ≠ ⊤ := fun k => by
    have hle : β k ≤ ∑ j, β j := Finset.single_le_sum (fun j _ => zero_le) (Finset.mem_univ k)
    rw [hβ] at hle
    exact ne_top_of_le_ne_top ENNReal.one_ne_top hle
  have hrtop : r ≠ ⊤ := by
    rw [hr_def]
    exact ENNReal.sum_ne_top.mpr fun k _ => ne_top_of_le_ne_top (hβtop k) tsub_le_self
  by_cases hr0 : r = 0
  · have heq : ∀ k, α k = β k := by
      have hβle : ∀ k, β k ≤ α k := by
        have hβmin : ∀ k, β k - min (α k) (β k) = 0 :=
          fun k => (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => zero_le)).mp hr0 k (Finset.mem_univ k)
        intro k
        exact (tsub_eq_zero_iff_le.mp (hβmin k)).trans (min_le_left _ _)
      have hsumeq : ∑ k, (α k - β k) = 0 := by
        rw [Finset.sum_tsub_of_le _ _ _ (fun k _ => hβtop k) (fun k _ => hβle k), hα, hβ, tsub_self]
      have hαle : ∀ k, α k ≤ β k := fun k =>
        tsub_eq_zero_iff_le.mp
          ((Finset.sum_eq_zero_iff_of_nonneg (fun k _ => zero_le)).mp hsumeq k (Finset.mem_univ k))
      exact fun k => le_antisymm (hαle k) (hβle k)
    have hμeq : (∑ k, β k • Measure.dirac (x k)) = ∑ k, α k • Measure.dirac (x k) :=
      Finset.sum_congr rfl fun k _ => by rw [heq k]
    rw [hμeq, W2_self_eq_zero, hr0]
    simp
  · set γ : Fin M → ℝ≥0∞ := fun k => min (α k) (β k) with hγ_def
    set μγ : Measure (Eucl d) := ∑ k, γ k • Measure.dirac (x k) with hμγ_def
    set A : Measure (Eucl d) := ∑ k, (β k - γ k) • Measure.dirac (x k) with hA_def
    set B : Measure (Eucl d) := ∑ k, (α k - γ k) • Measure.dirac (x k) with hB_def
    haveI : SFinite A := hA_def ▸ sFinite_sum_smul_dirac x (fun k => β k - γ k)
    haveI : SFinite B := hB_def ▸ sFinite_sum_smul_dirac x (fun k => α k - γ k)
    have hptalg : ∀ k, γ k + (β k - γ k) = β k := by
      intro k
      rcases le_total (α k) (β k) with h | h
      · rw [hγ_def]; simp only; rw [min_eq_left h]; exact add_tsub_cancel_of_le h
      · rw [hγ_def]; simp only; rw [min_eq_right h, tsub_self, add_zero]
    have hptalg2 : ∀ k, γ k + (α k - γ k) = α k := by
      intro k
      rcases le_total (α k) (β k) with h | h
      · rw [hγ_def]; simp only; rw [min_eq_left h, tsub_self, add_zero]
      · rw [hγ_def]; simp only; rw [min_eq_right h]; exact add_tsub_cancel_of_le h
    have hsumA : μγ + A = ∑ k, β k • Measure.dirac (x k) := by
      rw [hμγ_def, hA_def, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [← add_smul, hptalg k]
    have hsumB : μγ + B = ∑ k, α k • Measure.dirac (x k) := by
      rw [hμγ_def, hB_def, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [← add_smul, hptalg2 k]
    have hAuniv : A Set.univ = r := by
      rw [hA_def, sum_smul_dirac_univ, hr_def]
    have hBuniv : B Set.univ = r := by
      rw [hB_def, sum_smul_dirac_univ, hγ_def]
      have h1 : ∑ k, (α k - min (α k) (β k)) = 1 - ∑ k, min (α k) (β k) := by
        rw [Finset.sum_tsub_of_le _ _ _
          (fun k _ => ne_top_of_le_ne_top (hβtop k) (min_le_right _ _))
          (fun k _ => min_le_left _ _), hα]
      have h2 : r = 1 - ∑ k, min (α k) (β k) := by
        rw [hr_def, Finset.sum_tsub_of_le _ _ _
          (fun k _ => ne_top_of_le_ne_top (hβtop k) (min_le_right _ _))
          (fun k _ => min_le_right _ _), hβ]
      rw [h1, h2]
    have hAS : A (sphere d)ᶜ = 0 := by
      rw [hA_def]
      simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
      apply Finset.sum_eq_zero
      intro k _
      rw [Measure.dirac_apply' _ (measurableSet_sphere d).compl,
        Set.indicator_of_notMem (by simp [hx k])]
      ring
    have hBS : B (sphere d)ᶜ = 0 := by
      rw [hB_def]
      simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
      apply Finset.sum_eq_zero
      intro k _
      rw [Measure.dirac_apply' _ (measurableSet_sphere d).compl,
        Set.indicator_of_notMem (by simp [hx k])]
      ring
    have hcplγ : IsCoupling (μγ.map (fun z => (z, z))) μγ μγ := isCoupling_diagonal μγ
    have hcplAB : IsCoupling (r⁻¹ • (A.prod B)) A B :=
      isCoupling_scaled_prod hr0 hrtop hAuniv hBuniv
    have hcpl : IsCoupling (μγ.map (fun z => (z, z)) + r⁻¹ • (A.prod B))
        (∑ k, β k • Measure.dirac (x k)) (∑ k, α k • Measure.dirac (x k)) := by
      rw [← hsumA, ← hsumB]
      exact isCoupling_add hcplγ hcplAB
    have hcost : sqTransportCost (μγ.map (fun z => (z, z)) + r⁻¹ • (A.prod B)) ≤ 4 * r := by
      rw [sqTransportCost_add]
      have h1 : sqTransportCost (μγ.map (fun z => (z, z))) = 0 := sqTransportCost_diagonal μγ
      have h2 : sqTransportCost (r⁻¹ • (A.prod B)) ≤ 4 * r :=
        sqTransportCost_scaled_prod_le hAS hBS hr0 hrtop hAuniv hBuniv
      calc sqTransportCost (μγ.map (fun z => (z, z))) + sqTransportCost (r⁻¹ • (A.prod B))
          = sqTransportCost (r⁻¹ • (A.prod B)) := by rw [h1, zero_add]
        _ ≤ 4 * r := h2
    calc W2 (∑ k, β k • Measure.dirac (x k)) (∑ k, α k • Measure.dirac (x k))
        ≤ sqTransportCost (μγ.map (fun z => (z, z)) + r⁻¹ • (A.prod B)) ^ (2⁻¹ : ℝ) :=
          W2_le_rpow_sqTransportCost hcpl
      _ ≤ (4 * r) ^ (2⁻¹ : ℝ) := by gcongr
      _ = 4 ^ (2⁻¹ : ℝ) * r ^ (2⁻¹ : ℝ) := by rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      _ = 2 * r ^ (2⁻¹ : ℝ) := by
          congr 1
          rw [show (4:ℝ≥0∞) = 2^2 by norm_num, ← ENNReal.rpow_natCast (2:ℝ≥0∞) 2,
            ← ENNReal.rpow_mul]
          norm_num

end MeasureToMeasure
