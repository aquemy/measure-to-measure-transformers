import Regression.Refuted.F12_HeavyTails

/-!
# F18: the `lemma_3_2` family form is false without `2 ≤ d` (dimension one)

`lemma_3_2` (transport a sphere-supported probability family with a shared missing cap into the
positive orthant) was stated for arbitrary `d`. Instantiating at `d = 1` refutes that form:
the `0`-sphere is `S^0 = {±ω}`, and every block's velocity field is radially tangent
(`Block.radial`: `⟪x, field x⟫ = gate x · (‖x‖² − 1)`, so on the sphere `field x ⊥ x`); in
dimension one, orthogonality to a unit vector forces `field x = 0`
(`eucl1_ortho_unit_eq_zero`). Hence every block fixes `-ω` (`flowMap_fixed_of_forall_field_zero`),
so `δ_{-ω}` cannot be moved into the orthant `{+ω}` — while the sphere-support and
shared-missing-cap hypotheses at `d = 1` are jointly satisfiable (witnessed here by `μ = δ_{-e₀}`,
missing direction `ω = e₀`).

Repaired by adding `2 ≤ d` to the discharged `lemma_3_2` (finding F18), matching the paper's
`S^{d-1}, d ≥ 2` and the `lemma_B_1`/`lemma_B_2` precedent. This file kernel-checks
`Regression.OldLemma32FamilyNoDimSig → False`; the discharged theorem carries `2 ≤ d`, so it
cannot reproduce this signature.
-/

set_option autoImplicit false

namespace Regression.Refuted

open MeasureTheory MeasureToMeasure MeasureToMeasure.Axioms MeasureToMeasure.Statements
open scoped RealInnerProductSpace

/-- In `Eucl 1`, a vector orthogonal to a unit vector is zero: the coordinate identity
`⟪x, v⟫ = x₀ v₀` with `|x₀| = 1` forces `v₀ = 0`, hence `v = 0` (`Fin 1` is a subsingleton). -/
theorem eucl1_ortho_unit_eq_zero {x v : Eucl 1} (hx : ‖x‖ = 1)
    (h : (⟪x, v⟫ : ℝ) = 0) : v = 0 := by
  have hinner : (⟪x, v⟫ : ℝ) = x 0 * v 0 := by
    simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  have hxabs : |x 0| = 1 := by
    rw [← hx, EuclideanSpace.norm_eq]; simp [Real.sqrt_sq_eq_abs]
  have hxne : x 0 ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hxabs; norm_num at hxabs
  have hv0 : v 0 = 0 := by
    rw [hinner] at h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 hxne
    · exact h1
  ext i; rw [Subsingleton.elim i (0 : Fin 1)]; simpa using hv0

/-- In dimension one, every block's field vanishes on the sphere: radial tangency gives
`⟪x, field x⟫ = 0`, and `eucl1_ortho_unit_eq_zero` upgrades that to `field x = 0`. -/
theorem block_field_eq_zero_dim_one (b : Block 1) {x : Eucl 1} (hx : ‖x‖ = 1) :
    b.field x = 0 :=
  eucl1_ortho_unit_eq_zero hx (by rw [b.radial x, hx]; ring)

/-- **F18.** The `2 ≤ d`-free `lemma_3_2` family form is false: at `d = 1` the one-member family
`![δ_{-e₀}]` satisfies every hypothesis (probability, sphere-supported, shared missing cap toward
`e₀`), yet no schedule moves it into the orthant — the flow fixes `-e₀`, whose zeroth coordinate
is `-1 < 0`. -/
theorem oldLemma32Family_dimOne_false : ¬ Regression.OldLemma32FamilyNoDimSig := by
  intro h
  set e : Eucl 1 := EuclideanSpace.single (0 : Fin 1) (1 : ℝ) with he
  have hnorm_neg : ‖-e‖ = 1 := by rw [norm_neg, he]; simp
  -- Shared missing direction `ω = e₀`, gap `δ = 1`: `⟪e₀, -e₀⟫ = -1 ≤ 0`.
  have hmiss : SharedMissingDirection (fun _ : Fin 1 => Measure.dirac (-e)) := by
    refine ⟨e, by rw [he]; simp, 1, one_pos, fun _ => ?_⟩
    have hmem : (-e) ∈ {x : Eucl 1 | (⟪e, x⟫ : ℝ) ≤ 1 - 1} := by
      simp only [Set.mem_setOf_eq, inner_neg_right, real_inner_self_eq_norm_sq, he]
      simp
    have hms : MeasurableSet {x : Eucl 1 | (⟪e, x⟫ : ℝ) ≤ 1 - 1} :=
      measurableSet_le (by fun_prop) measurable_const
    show Measure.dirac (-e) {x : Eucl 1 | (⟪e, x⟫ : ℝ) ≤ 1 - 1}ᶜ = 0
    rw [Measure.dirac_apply' _ hms.compl, Set.indicator_of_notMem (not_not_intro hmem)]
  obtain ⟨θ, _hsw, horth⟩ :=
    h (fun _ : Fin 1 => Measure.dirac (-e)) (fun _ => inferInstance) 1 one_pos
      (fun _ => by
        have hsm : MeasurableSet (sphere 1) := Metric.isClosed_sphere.measurableSet
        have hmemS : (-e) ∈ sphere 1 := by
          rw [sphere, Metric.mem_sphere, dist_zero_right]; exact hnorm_neg
        show Measure.dirac (-e) (sphere 1)ᶜ = 0
        rw [Measure.dirac_apply' _ hsm.compl,
          Set.indicator_of_notMem (not_not_intro hmemS)]) hmiss
  -- Every block fixes `-e₀`, so the pushforward is `δ_{-e₀}` again.
  have hfix : flowMap θ 1 (-e) = -e :=
    flowMap_fixed_of_forall_field_zero θ 1 (fun b _ => block_field_eq_zero_dim_one b hnorm_neg)
  have hmapdirac : measureFlow θ 1 (Measure.dirac (-e)) = Measure.dirac (-e) := by
    show (Measure.dirac (-e)).map (flowMap θ 1) = Measure.dirac (-e)
    rw [Measure.map_dirac (-e), hfix]
  -- `-e₀ ∉ orthant 1` because its zeroth coordinate is `-1`.
  have hnot : (-e) ∉ orthant 1 := by
    intro hmem
    have h0 := hmem 0
    have hval : (-e) 0 = -1 := by rw [he]; simp
    rw [hval] at h0; norm_num at h0
  have hbad := horth 0
  rw [hmapdirac] at hbad
  change Measure.dirac (-e) (orthant 1)ᶜ = 0 at hbad
  rw [Measure.dirac_apply' _ measurableSet_orthant1.compl, Set.indicator_of_mem hnot] at hbad
  exact one_ne_zero hbad

end Regression.Refuted
