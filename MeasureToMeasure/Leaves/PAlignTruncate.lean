import MeasureToMeasure.Leaves.TaylorRemainderBound

/-!
# Duration-truncating a `pAlign` mean-field flow (`lemma_3_4_part2` non-vacuous re-discharge, G2)

Gap (i) of the non-vacuous `lemma_3_4_part2` re-discharge campaign: the asymmetric-cap route's
Phase 1 axiom hands us a raw `IsMeanFieldFlow (pAlign T hT) μ Φ` witness, and the downstream
schedule machinery consumes `attnStep` of a schedule block, evaluated at some intermediate time
`Tstar ≤ T`. The `V = 0` `blockFlow` bridge (`isMeanFieldFlow_blockFlow` +
`attnStep_eq_map_blockFlow`) is inapplicable here because `pAlign` has `V = id`, so the correct
route is *duration truncation*: `pAlign τ` and `pAlign T` share `V, B, W, U, b` definitionally
(only `.duration` differs), hence a mean-field flow for the long block restricts clause-wise to
one for the short block (`isMeanFieldFlow_pAlign_mono`), and `meanFieldFlow_unique` then
identifies `attnStep (pAlign τ) μ` with `μ.map (Φ τ)` (`attnStep_pAlign_eq_map`), copying the
proof shape of `attnStep_rescale_eq` (`AttnRescale.lean`).

M3b/mid-level staging: consumed when `lemma_3_4_part2` is non-vacuously re-discharged; see
`Statements/MidLevel.lean`.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Set
open MeasureToMeasure.Foundations

variable {d : ℕ}

/-- **Duration truncation of a `pAlign` mean-field flow.** A mean-field flow of the alignment
block `pAlign T` is also a mean-field flow of the truncated block `pAlign τ` for any
`0 ≤ τ ≤ T`: `init` is verbatim, `measurable`/`lipschitz`/`sphere_bijOn`/`deriv` restrict along
`Set.Icc 0 τ ⊆ Set.Icc 0 T`, and the `deriv` clause's field term is unchanged because
`AttnParams.field` reads only `V, B, W, U, b`, which `pAlign τ` and `pAlign T` share
definitionally. -/
theorem isMeanFieldFlow_pAlign_mono {μ : Measure (Eucl d)} {Φ : ℝ → Eucl d → Eucl d}
    {T τ : ℝ} (hτ0 : 0 ≤ τ) (hτT : τ ≤ T) (hT : 0 ≤ T)
    (h : IsMeanFieldFlow (pAlign T hT) μ Φ) :
    IsMeanFieldFlow (pAlign τ hτ0) μ Φ := by
  have hsub : Set.Icc (0:ℝ) τ ⊆ Set.Icc (0:ℝ) T := Set.Icc_subset_Icc_right hτT
  constructor
  · exact h.init
  · intro t ht; exact h.measurable t (hsub ht)
  · obtain ⟨L, hL⟩ := h.lipschitz; exact ⟨L, fun t ht => hL t (hsub ht)⟩
  · intro t ht; exact h.sphere_bijOn t (hsub ht)
  · intro x hx t ht; exact h.deriv x hx t (hsub ht)

/-- **`attnStep` of a truncated `pAlign` block is the flow's time-`τ` pushforward.** Given any
mean-field-flow witness `Φ` for `pAlign T` on a sphere-supported probability measure, the
schedule-level step of the truncated block `pAlign τ` (for `0 ≤ τ ≤ T`) is exactly `μ.map (Φ τ)`:
truncation (`isMeanFieldFlow_pAlign_mono`) makes `Φ` a witness for `pAlign τ`, and
`meanFieldFlow_unique` identifies it on the sphere with the flow `attnStep` chose. This is the
G2 bridge from the Phase-1 axiom's raw flow output at an intermediate time to the `attnStep`
schedule vocabulary. -/
theorem attnStep_pAlign_eq_map [NeZero d] (μ : Measure (Eucl d)) [IsProbabilityMeasure μ]
    (hs : μ (sphere d)ᶜ = 0) {T τ : ℝ} (hT : 0 ≤ T) {Φ : ℝ → Eucl d → Eucl d}
    (hΦ : IsMeanFieldFlow (pAlign T hT) μ Φ) (hτ : 0 ≤ τ) (hτT : τ ≤ T) :
    attnStep (pAlign τ hτ) μ = μ.map (Φ τ) := by
  have hΦτ : IsMeanFieldFlow (pAlign τ hτ) μ Φ := isMeanFieldFlow_pAlign_mono hτ hτT hT hΦ
  have heq := meanFieldFlow_unique hs
    (@exists_meanFieldFlow d (pAlign τ hτ) μ ‹_› hs).choose_spec hΦτ
    (pAlign τ hτ).duration ⟨(pAlign τ hτ).duration_nonneg, le_rfl⟩
  unfold attnStep
  rw [dif_pos ⟨‹IsProbabilityMeasure μ›, hs⟩]
  refine Measure.map_congr ?_
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun x hx => ?_) hs
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff] at hx ⊢
  intro hxs
  apply hx
  rw [heq x hxs]
  rfl

end MeasureToMeasure.Leaves
