import MeasureToMeasure.Foundations.Attention
import MeasureToMeasure.Foundations.AttnStepExistence
import MeasureToMeasure.Leaves.DivergenceFormula

/-!
# Rescaling a mean-field flow's block and duration (`exists_parked_schedule` leaf 2)

`exists_parked_schedule` (Appendix B) needs a genuine schedule-*duration-budget* fact: the paper's
own mechanism (Prop. 2.2, p.11) partitions the OVERALL duration `T` into `N` sequential
sub-intervals, one per family member, rather than concatenating `N` full-duration-`T` copies. Each
member's steering block must therefore be rescaled to fit its (shorter) allotted sub-interval.

This leaf is the reparametrization fact that makes that legal: if `Φ` is a mean-field flow of block
`p` on `[0, p.duration]`, then scaling `p`'s `V, W` by `N` (keeping `B, U, b` fixed) and running for
duration `p.duration / N` gives `Ψ(s) := Φ(N·s)`, which IS a mean-field flow of the rescaled block
on `[0, p.duration / N]`, reaching the SAME endpoint `Ψ(p.duration/N) = Φ(p.duration)`.

**Why the field scales by `N`.** `AttnParams.field` is `x ↦ P_x^⊥(V(attnAvg B μ x) + W(reluVec(Ux+b)))`;
scaling `V, W` by `N` scales the argument of `tangentialProjector` by `N`, and `tangentialProjector`
is linear in its vector argument (`tangentialProjector_smul_right`), so the rescaled field is exactly
`N` times the original -- matching the `N`-fold speedup the chain rule needs for `s ↦ Φ(Ns)`'s
derivative to solve the rescaled block's mean-field ODE.

M3b/mid-level staging: consumed when `exists_parked_schedule` is discharged; see
`Statements/MidLevel.lean`.
-/

namespace MeasureToMeasure.Foundations

variable {d : ℕ}

/-- The `AttnParams` block with `V, W` scaled by `N` and duration divided by `N` (keeping `B, U, b`
fixed). Paired with the time reparametrization `s ↦ N·s`, this is what lets a schedule fit a
shorter sub-interval while reaching the same endpoint. -/
noncomputable def AttnParams.rescale (p : AttnParams d) {N : ℝ} (hN : 0 < N) : AttnParams d where
  V := N • p.V
  B := p.B
  W := N • p.W
  U := p.U
  b := p.b
  duration := p.duration / N
  duration_nonneg := div_nonneg p.duration_nonneg hN.le

@[simp] theorem AttnParams.rescale_duration (p : AttnParams d) {N : ℝ} (hN : 0 < N) :
    (p.rescale hN).duration = p.duration / N := rfl

end MeasureToMeasure.Foundations

namespace MeasureToMeasure.Leaves

open MeasureTheory Set
open scoped RealInnerProductSpace
open MeasureToMeasure.Foundations

variable {d : ℕ}

/-- The rescaled block's field is exactly `N` times the original field, at every measure and point. -/
theorem AttnParams.field_rescale (p : AttnParams d) {N : ℝ} (hN : 0 < N)
    (μ : Measure (Eucl d)) (x : Eucl d) :
    (p.rescale hN).field μ x = N • p.field μ x := by
  unfold AttnParams.field AttnParams.rescale
  simp only [smul_apply, smul_add, ← tangentialProjector_smul_right]

/-- **The rescaling lemma.** A mean-field flow of `p` on `[0, p.duration]` reparametrizes, under
`s ↦ N·s`, into a mean-field flow of `p`'s `N`-rescaled block on `[0, p.duration / N]`. -/
theorem isMeanFieldFlow_rescale {p : AttnParams d} {μ₀ : Measure (Eucl d)}
    {Φ : ℝ → Eucl d → Eucl d} (hΦ : IsMeanFieldFlow p μ₀ Φ) {N : ℝ} (hN : 0 < N) :
    IsMeanFieldFlow (p.rescale hN) μ₀ (fun s x => Φ (N * s) x) := by
  set p' := p.rescale hN with hp'
  have hmapsto : ∀ s ∈ Set.Icc (0 : ℝ) p'.duration, N * s ∈ Set.Icc (0 : ℝ) p.duration := by
    intro s hs
    rw [hp', AttnParams.rescale_duration] at hs
    refine ⟨by positivity [hs.1], ?_⟩
    linarith [(le_div_iff₀ hN).mp hs.2]
  constructor
  · funext x; simp [hΦ.init]
  · intro s hs; exact hΦ.measurable (N * s) (hmapsto s hs)
  · obtain ⟨L, hL⟩ := hΦ.lipschitz
    exact ⟨L, fun s hs => hL (N * s) (hmapsto s hs)⟩
  · intro s hs; exact hΦ.sphere_bijOn (N * s) (hmapsto s hs)
  · intro x hx s hs
    have hd : HasDerivAt (fun t => Φ t x) (p.field (μ₀.map (Φ (N * s))) (Φ (N * s) x)) (N * s) :=
      hΦ.deriv x hx (N * s) (hmapsto s hs)
    have hinner : HasDerivAt (fun s : ℝ => N * s) N s := by
      simpa using (hasDerivAt_id s).const_mul N
    have hcomp := hd.scomp s hinner
    have hfield : p'.field (μ₀.map ((fun s' y => Φ (N * s') y) s)) ((fun s' y => Φ (N * s') y) s x)
        = N • p.field (μ₀.map (Φ (N * s))) (Φ (N * s) x) := by
      simp only
      exact AttnParams.field_rescale p hN _ _
    rw [hfield]
    exact hcomp

/-- **Rescaling a block doesn't change its `attnStep`.** The `N`-rescaled block, run for its own
(shorter) duration, pushes a sphere-supported probability measure forward to the SAME measure as
the original block run for its own duration -- both are witnessed by reparametrized copies of the
SAME underlying trajectory, and `meanFieldFlow_unique` identifies any two witnesses on the sphere.
This is the piece that lets `lemma_3_4_part2`'s exact `durationSum θ = T` requirement be met: a
schedule built as a single block of duration `n·T` (for the reach budget the mass-gap-cap-collapse
construction needs) can be swapped for its `n`-rescaled form, of duration EXACTLY `T`, with no
change to the resulting measure. -/
theorem attnStep_rescale_eq (p : AttnParams d) [NeZero d] {N : ℝ} (hN : 0 < N)
    (μ : Measure (Eucl d)) [IsProbabilityMeasure μ] (hs : μ (sphere d)ᶜ = 0) :
    attnStep (p.rescale hN) μ = attnStep p μ := by
  have hΦ := (@exists_meanFieldFlow d p μ ‹_› hs).choose_spec
  set Φ := (@exists_meanFieldFlow d p μ ‹_› hs).choose with hΦdef
  have hΨ : IsMeanFieldFlow (p.rescale hN) μ (fun s x => Φ (N * s) x) :=
    isMeanFieldFlow_rescale hΦ hN
  have heq := meanFieldFlow_unique hs (@exists_meanFieldFlow d (p.rescale hN) μ ‹_› hs).choose_spec
    hΨ (p.rescale hN).duration ⟨(p.rescale hN).duration_nonneg, le_rfl⟩
  unfold attnStep
  rw [dif_pos ⟨‹IsProbabilityMeasure μ›, hs⟩, dif_pos ⟨‹IsProbabilityMeasure μ›, hs⟩]
  refine Measure.map_congr ?_
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun x hx => ?_) hs
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff] at hx ⊢
  intro hxs
  apply hx
  rw [heq x hxs]
  show Φ (N * (p.rescale hN).duration) x = Φ p.duration x
  congr 2
  rw [AttnParams.rescale_duration]
  field_simp

/-- Singleton-schedule form of `attnStep_rescale_eq`: rescaling a single-block schedule's block
doesn't change the resulting measure. -/
theorem attnMeasureFlow_singleton_rescale_eq (p : AttnParams d) [NeZero d] {N : ℝ} (hN : 0 < N)
    (μ : Measure (Eucl d)) [IsProbabilityMeasure μ] (hs : μ (sphere d)ᶜ = 0) :
    attnMeasureFlow [p.rescale hN] μ = attnMeasureFlow [p] μ :=
  attnStep_rescale_eq p hN μ hs

end MeasureToMeasure.Leaves
