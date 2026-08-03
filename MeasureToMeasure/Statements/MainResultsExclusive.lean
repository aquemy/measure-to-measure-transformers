import MeasureToMeasure.Statements.MainResults
import MeasureToMeasure.Leaves.DisentangleInductionAssembly

/-!
# Companion main results on the exclusive-supports gate

Companions of `prop_3_1`, `theorem_1_1`, and `theorem_1_2` (`Statements/MainResults.lean`) whose
statements are the originals' verbatim plus ONE extra hypothesis, the
`Leaves.ExclusiveSupportFamily` gate (every member of the family owns a support point outside the
union of the other members' supports). On the gate the axiom `exists_disentangling_balls` is
replaced by its machine-checked companion
`Leaves.exists_disentangling_balls_of_exclusive_supports`
(`Leaves/DisentangleInductionAssembly.lean`, finding F27); everything else in each proof is the
original's body unchanged.

**Honest status.** These companions are NOT fully machine-checked: the kernel closure of every
theorem in this file is `{propext, Classical.choice, Quot.sound, lemma_3_3}`, since the gated
disentangler still consumes the `lemma_3_3` axiom (the paper's Lemma 3.3 collapse step,
`Statements/MidLevel.lean`). Effective CKC status `math.axiomatised`.

**Honest narrowing.** The paper's Theorems 1.1/1.2 and Proposition 3.1 (arXiv:2411.04551v3) carry
NO exclusivity gate: they claim the full generality in which distinct members may share supports
entirely. That general case stays on the untouched public axiom `exists_disentangling_balls` and
the original theorems in `MainResults.lean`, which gain no hypothesis here. The gate is what makes
the formal Section 3.3 placement chain close today (findings F17(b), F22, F27); discharging the
general case is the separate equal-supports follow-up campaign.

Statement-fidelity conventions: `hne` (the paper's standing pairwise-distinctness assumption,
p. 5) keeps the originals' exact unprefixed shape, consumed here through the axiom-shaped call
into the gated companion (whose own `_hne` is fidelity-retained); `_hmiss₁` in the Theorem 1.2
companion is retained underscore-prefixed exactly as in the original.
-/

namespace MeasureToMeasure.Statements

open MeasureTheory MeasureToMeasure.Axioms
open MeasureToMeasure.Foundations (AttnSchedule attnMeasureFlow)
open scoped RealInnerProductSpace

variable {d : ℕ}

/-- **Proposition 3.1 companion on the exclusive-supports gate.** `prop_3_1`'s exact statement
plus `hgate : Leaves.ExclusiveSupportFamily μ₀`: under a shared missing direction, a family whose
members each own an exclusive support point admits a schedule whose solution map renders the
supports pairwise disjoint, each concentrated in an open hemisphere.

Proof: `prop_3_1`'s body verbatim, with the axiom call `exists_disentangling_balls` swapped for
the machine-checked gated companion `Leaves.exists_disentangling_balls_of_exclusive_supports`.
Kernel closure `{propext, Classical.choice, Quot.sound, lemma_3_3}`, NOT axiom-free: the gated
disentangler still rests on the `lemma_3_3` axiom. The paper's Proposition 3.1 carries no
exclusivity gate; the general shared-supports case stays on the untouched axiom (see the module
docstring). -/
theorem prop_3_1_of_exclusive_supports (hd : 3 ≤ d) {N : ℕ}
    (μ₀ : Fin N → Measure (Eucl d)) (T : ℝ) (hT : 0 < T)
    (hμ : ∀ i, IsProbabilityMeasure (μ₀ i))
    (hμs : ∀ i, supportedIn (μ₀ i) (sphere d))
    (hne : Pairwise fun i j => μ₀ i ≠ μ₀ j)
    (hmiss : SharedMissingDirection μ₀)
    (hgate : Leaves.ExclusiveSupportFamily μ₀) :
    ∃ θ : AttnSchedule d, AttnSchedule.durationSum θ = T ∧
      DisjointSupports (fun i => attnMeasureFlow θ (μ₀ i)) ∧
      ∀ i, ∃ e : Eucl d, ‖e‖ = 1 ∧ supportedIn (attnMeasureFlow θ (μ₀ i)) {x | 0 < ⟪e, x⟫} := by
  obtain ⟨θ, α, r, hdur, hr0, hr1, hα, hsep, hsupp, -⟩ :=
    Leaves.exists_disentangling_balls_of_exclusive_supports hd μ₀ T hT hμ hμs hne hmiss hgate
  -- Each carrier ball lies in the open hemisphere around its centre direction.
  have hball_hemi : ∀ (i : Fin N) (x : Eucl d), x ∈ Metric.ball (α i) r → 0 < ⟪α i, x⟫ := by
    intro i x hx
    rw [Metric.mem_ball] at hx
    have hnorm : ‖x - α i‖ < r := by rw [← dist_eq_norm]; exact hx
    have hself : ⟪α i, α i⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, hα i]; norm_num
    have hbound : -‖x - α i‖ ≤ ⟪α i, x - α i⟫ := by
      have habs := abs_real_inner_le_norm (α i) (x - α i)
      rw [hα i, one_mul] at habs
      have := (abs_le.mp habs).1
      linarith
    have hexp : ⟪α i, x⟫ = ⟪α i, x - α i⟫ + ⟪α i, α i⟫ := by
      rw [inner_sub_right]; ring
    rw [hexp, hself]
    linarith
  refine ⟨θ, hdur, ⟨fun i => Metric.ball (α i) r, hsupp, ?_⟩, ?_⟩
  · -- The carrier balls are pairwise disjoint because their centres are `2r`-separated.
    intro i j hij
    exact Metric.ball_disjoint_ball (by linarith [hsep i j hij])
  · -- Each measure is supported in the hemisphere around its centre direction.
    intro i
    refine ⟨α i, hα i, ?_⟩
    have hsub : Metric.ball (α i) r ⊆ {x | 0 < ⟪α i, x⟫} := fun x hx => hball_hemi i x hx
    exact measure_mono_null (Set.compl_subset_compl.mpr hsub) (hsupp i)

/-- **Theorem 1.1 companion on the exclusive-supports gate** (Dirac targets). `theorem_1_1`'s
exact statement plus `hgate : Leaves.ExclusiveSupportFamily μ₀`: under a shared missing direction,
a family whose members each own an exclusive support point is steered by one schedule to within
`ε` of the point-mass targets `δ_{x i}` in `W₂`.

Proof: `theorem_1_1`'s body verbatim, with the call to `prop_3_1` swapped for the gated companion
`prop_3_1_of_exclusive_supports` (extra argument `hgate`); the machine-checked second half
(`exists_parked_schedule_of_map_targets` with constant maps, the `Measure.map_const` Dirac
identification, and the `attnMeasureFlow_append` concatenation) is unchanged. Kernel closure
`{propext, Classical.choice, Quot.sound, lemma_3_3}`, NOT axiom-free: the gated disentangler
still rests on the `lemma_3_3` axiom. The paper's Theorem 1.1 carries no exclusivity gate; the
general shared-supports case stays on the original `theorem_1_1` and the untouched axiom (see the
module docstring). -/
theorem theorem_1_1_of_exclusive_supports (hd : 3 ≤ d) {N : ℕ}
    (μ₀ : Fin N → Measure (Eucl d)) (x : Fin N → Eucl d)
    (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε) (hmiss : SharedMissingDirection μ₀)
    (hμ : ∀ i, IsProbabilityMeasure (μ₀ i))
    (hμs : ∀ i, supportedIn (μ₀ i) (sphere d)) (hx : ∀ i, x i ∈ sphere d)
    (hne : Pairwise fun i j => μ₀ i ≠ μ₀ j)
    (hgate : Leaves.ExclusiveSupportFamily μ₀) :
    ∃ θ : AttnSchedule d, AttnSchedule.durationSum θ = T ∧
      ∀ i, Axioms.W2 (attnMeasureFlow θ (μ₀ i)) (Measure.dirac (x i)) ≤ ε := by
  have hT2 : 0 < T / 2 := by linarith
  obtain ⟨θ₁, hdur₁, hdisj, -⟩ :=
    prop_3_1_of_exclusive_supports hd μ₀ (T / 2) hT2 hμ hμs hne hmiss hgate
  have hν : ∀ i, IsProbabilityMeasure (attnMeasureFlow θ₁ (μ₀ i)) := fun i =>
    haveI := hμ i
    Foundations.isProbabilityMeasure_attnMeasureFlow θ₁ (μ₀ i) (hμs i)
  have hνs : ∀ i, supportedIn (attnMeasureFlow θ₁ (μ₀ i)) (sphere d) := fun i =>
    Foundations.attnMeasureFlow_supportedIn_sphere θ₁ (μ₀ i) (hμs i)
  -- One schedule steers every member to its (constant-map pushforward) Dirac target.
  obtain ⟨Θ, hdurΘ, hΘ⟩ :=
    exists_parked_schedule_of_map_targets hd (fun i => attnMeasureFlow θ₁ (μ₀ i))
      (fun i _ => x i) (T / 2) ε hT2 hε hν hνs hdisj (fun _ => measurable_const)
      (fun i => Filter.Eventually.of_forall fun _ => hx i)
  refine ⟨θ₁ ++ Θ, ?_, fun i => ?_⟩
  · rw [AttnSchedule.durationSum_append, hdur₁, hdurΘ]; ring
  · rw [Foundations.attnMeasureFlow_append]
    -- The constant-map pushforward of a probability measure is the Dirac at the target point.
    have hmap : (attnMeasureFlow θ₁ (μ₀ i)).map (fun _ => x i) = Measure.dirac (x i) := by
      haveI := hν i
      rw [Measure.map_const, measure_univ, one_smul]
    simpa [hmap] using hΘ i

end MeasureToMeasure.Statements
