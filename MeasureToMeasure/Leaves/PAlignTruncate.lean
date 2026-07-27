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
one for the short block (`isMeanFieldFlow_pAlign_mono`, this file). The follow-up leaf
(`attnStep_pAlign_eq_map`) then uses `meanFieldFlow_unique` to identify `attnStep (pAlign τ) μ`
with `μ.map (Φ τ)`, copying the proof shape of `attnStep_rescale_eq` (`AttnRescale.lean`).

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

end MeasureToMeasure.Leaves
