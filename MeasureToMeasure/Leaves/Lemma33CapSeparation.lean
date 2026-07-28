import MeasureToMeasure.Leaves.AsymmetricCapCollapse
import MeasureToMeasure.Leaves.OrthantBoundaryGap
import MeasureToMeasure.Leaves.GeodesicHullConvex

/-!
# Gated companion of `lemma_3_3`: cap-separation route

Paper source: Lemma 3.3, p.16, arXiv:2411.04551v3, via the Appendix B.2 Step 2 machinery ONLY
(the perceptron-gated support collapse of display (B.12), p.34). The axiom `lemma_3_3`
(`Statements/MidLevel.lean`) asserts the paper's full conclusion from the paper's own hypotheses;
its §3.3/§B.2 proof reaches that conclusion through a `Ψ₁⁻¹ ∘ Ψ₂ ∘ Ψ₁` conjugation whose parking
phase `Ψ₁` (a mean-field sweep plus its exact reversal) is unbuilt here. This companion proves the
SAME conclusion under an extra *cap-separation gate* that replaces the parking phase: the acted
member `μ₀ j` and its colinear companion `ν₀` already sit inside the closed sub-cap
`{m ≤ ⟪ω̂, ·⟫}` around the normalized barycenter direction
`ω̂ := ‖ℰ_{μ₀ʲ}‖⁻¹ • ℰ_{μ₀ʲ}`, while every bystander `μ₀ i` (`i ≠ j`) puts NO mass on the wider
open cap `{cosR < ⟪ω̂, ·⟫}` (`-1 ≤ cosR < m < 1`). Under that gate the whole conclusion is one
application of the mean-field support-collapse engine
(`exists_collapse_block_support_close`): a single self-centered attention block of duration
exactly `T` carries every sphere measure in the sub-cap into `Metric.ball ω̂ ε` and fixes every
off-cap sphere measure exactly.

The axiom `lemma_3_3` REMAINS; this companion does not narrow it. Every hypothesis of the axiom is
kept verbatim (house rule: hypotheses this route does not consume are underscore-prefixed, never
dropped -- the paper's scope needs them). The orthant hypothesis `hμo j` (with `hμs j`) is the one
place the normalized direction is shown genuinely unit: an orthant-and-sphere-supported
probability measure has a strictly positive barycenter (`norm_barycenter_pos_of_orthant`).

Probe fact recorded for consumers (see the non-vacuity witness in
`Regression/NonVacuity/Lemma33CapSeparation.lean`): for `N ≥ 2` the bystander clause forces
`cosR ≥ 0`, because orthant-supported bystanders always carry mass in the closed positive
hemisphere `{0 ≤ ⟪ω̂, ·⟫}` of the orthant direction `ω̂`, so any gate with `cosR < 0` is
unsatisfiable there; the witness instantiates the gate at `cosR = 24/25`.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory MeasureToMeasure.Foundations MeasureToMeasure.Statements
open scoped RealInnerProductSpace

variable {d : ℕ}

/-- **Lemma 3.3's conclusion under a cap-separation gate** (paper Lemma 3.3, p.16, via B.2 Step 2's
perceptron-gated support collapse, display (B.12), p.34). All hypotheses of the `lemma_3_3` axiom
verbatim, PLUS the gate: with `ω̂ := ‖ℰ_{μ₀ʲ}‖⁻¹ • ℰ_{μ₀ʲ}` the acted member and its companion are
carried by the closed sub-cap `{m ≤ ⟪ω̂, ·⟫}` and every bystander is null on the open cap
`{cosR < ⟪ω̂, ·⟫}` (`-1 ≤ cosR < m < 1`). Conclusion identical to the axiom's: one schedule of
total duration `T` confines BOTH `ν₀` and `μ₀ j` to `Metric.ball ω̂ ε` while restoring every other
member exactly. The gate replaces the paper's `Ψ₁` parking phase (mean-field sweep + reversal),
which is the unbuilt part of the axiom's proof; the axiom itself remains. -/
theorem lemma_3_3_of_cap_separation {N : ℕ} (j : Fin N) (μ₀ : Fin N → Measure (Eucl d))
    (ν₀ : Measure (Eucl d)) (hμ : ∀ i, IsProbabilityMeasure (μ₀ i)) [IsProbabilityMeasure ν₀]
    (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (hμs : ∀ i, supportedIn (μ₀ i) (sphere d)) (hμo : ∀ i, supportedIn (μ₀ i) (orthant d))
    (hνs : supportedIn ν₀ (sphere d)) (_hνo : supportedIn ν₀ (orthant d))
    (_hnoncol : Pairwise fun i k => ∀ c : ℝ, barycenter (μ₀ i) ≠ c • barycenter (μ₀ k))
    (_hνcol : ∃ c : ℝ, barycenter ν₀ = c • barycenter (μ₀ j))
    {cosR m : ℝ} (hcosR : (-1 : ℝ) ≤ cosR) (hmR : cosR < m) (hm1 : m < 1)
    (hjcap : supportedIn (μ₀ j)
      {x : Eucl d | m ≤ (⟪‖barycenter (μ₀ j)‖⁻¹ • barycenter (μ₀ j), x⟫ : ℝ)})
    (hνcap : supportedIn ν₀
      {x : Eucl d | m ≤ (⟪‖barycenter (μ₀ j)‖⁻¹ • barycenter (μ₀ j), x⟫ : ℝ)})
    (hbyst : ∀ i, i ≠ j →
      (μ₀ i) {x : Eucl d | cosR < (⟪‖barycenter (μ₀ j)‖⁻¹ • barycenter (μ₀ j), x⟫ : ℝ)} = 0) :
    ∃ θ : AttnSchedule d, AttnSchedule.durationSum θ = T ∧
      supportedIn (attnMeasureFlow θ ν₀)
        (Metric.ball (‖barycenter (μ₀ j)‖⁻¹ • barycenter (μ₀ j)) ε) ∧
      supportedIn (attnMeasureFlow θ (μ₀ j))
        (Metric.ball (‖barycenter (μ₀ j)‖⁻¹ • barycenter (μ₀ j)) ε) ∧
      ∀ i, i ≠ j → attnMeasureFlow θ (μ₀ i) = μ₀ i := by
  haveI := hμ j
  -- `d ≠ 0`: at `d = 0` the sphere is empty and cannot carry the probability measure `μ₀ j`
  haveI : NeZero d := by
    refine ⟨fun hd0 => ?_⟩
    have h := hμs j
    rw [supportedIn] at h
    have hemp : sphere d = (∅ : Set (Eucl d)) := by
      subst hd0
      ext x
      simp only [MeasureToMeasure.sphere, Metric.mem_sphere, dist_zero_right,
        Set.mem_empty_iff_false, iff_false]
      rw [Subsingleton.elim x 0]; simp
    rw [hemp, Set.compl_empty, measure_univ] at h
    exact one_ne_zero h
  -- the collapse direction is genuinely unit: orthant + sphere support force `ℰ_{μ₀ʲ} ≠ 0`
  have hbpos : 0 < ‖barycenter (μ₀ j)‖ :=
    norm_barycenter_pos_of_orthant (hμs j) (integrable_id_of_sphere_support (hμs j)) (hμo j)
  set ω : Eucl d := ‖barycenter (μ₀ j)‖⁻¹ • barycenter (μ₀ j) with hωdef
  have hω : ‖ω‖ = 1 := by
    rw [hωdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hbpos.ne']
  -- ONE self-centered block serves both cap-carried measures and every bystander
  obtain ⟨p, hdur, hcollapse, hfix, _⟩ :=
    exists_collapse_block_support_close (z := ω) hω hcosR hmR hm1 hT hε
  refine ⟨[p], ?_, ?_, ?_, ?_⟩
  · simp [AttnSchedule.durationSum, hdur]
  · exact hcollapse ν₀ hνs hνcap
  · exact hcollapse (μ₀ j) (hμs j) hjcap
  · intro i hi
    haveI := hμ i
    exact hfix (μ₀ i) (hμs i) (hbyst i hi)

end MeasureToMeasure.Leaves
