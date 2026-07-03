import MeasureToMeasure.Foundations.Sphere
import MeasureToMeasure.Foundations.Projector
import MeasureToMeasure.Foundations.FlowMap
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The self-attention mean-field flow interface (eq. (1.2); milestone M3b)

The paper's Transformer dynamics is the continuity equation driven by the *measure-dependent*
velocity field (eq. (1.2), p. 2)

  `v[μ](t, x) = P_x^⊥ ( V(t) · A_B[μ](t, x) + W(t) · (U(t) x + b(t))₊ )`,

where `A_B[μ](x) = (∫ e^{⟪Bx, z⟫} z dμ(z)) / (∫ e^{⟪Bx, ζ⟫} dμ(ζ))` is the measure-valued softmax
(self-attention) average. The measure dependence is *essential*: eq. (1.7) (p. 8) exhibits data
that no single-valued map -- hence no linear continuity equation, i.e. no fixed pushforward
`μ ↦ Φ_# μ` -- can interpolate, and review finding F14 machine-checked that the linear
`measureFlow` model of `Axioms/ContinuityEquation.lean` cannot host the paper's disentanglement
step for exactly this reason.

This file provides the faithful interface:

* `AttnParams` -- one constant-in-time Transformer block `(V, B, W, U, b)` with its duration
  (the paper's piecewise-constant parameters; a schedule is a `List`, and `switches` counts the
  constant pieces, the convention already used by the linear `Params`).
* `reluVec`, `attnAvg`, `AttnParams.field` -- the coordinatewise ReLU, the softmax average, and
  the velocity field (1.2), all as *concrete definitions* (Bochner integrals; junk values off the
  intended domain are harmless because every statement carries sphere-probability hypotheses).
* `IsMeanFieldFlow` -- the characteristics predicate: `Φ : ℝ → Eucl d → Eucl d` solves
  `d/dt Φ_t x = field (μ₀.map Φ_t) (Φ_t x)` on the sphere, starting from the identity, each time
  slice measurable, Lipschitz, and a bijection of the sphere (the regularity the paper's
  `φ^t` carries, eq. (B.2)).
* `exists_meanFieldFlow` / `meanFieldFlow_unique` -- the ONLY axioms: well-posedness of this
  McKean-Vlasov system on the sphere for sphere-supported probability data. Mathlib `v4.31.0`
  has no mean-field / measure-dependent ODE theory; this is the honest completion of milestone M3
  (the linear characteristic flow of `Foundations/FlowMap.lean` covers the measure-independent
  special case).
* `AttnSchedule`, `attnMeasureFlow` -- the solution operator of a schedule, by folding the
  per-block flow; composition over `++` is definitional (`attnMeasureFlow_append`).

**The linear bridge (`attnStep_eq_map_blockFlow`):** for a block with `V = 0` the field is
measure-independent (`AttnParams.field_of_V_eq_zero`); any linear `Block` whose field agrees with
it on the sphere realizes a mean-field flow (`isMeanFieldFlow_blockFlow`), so by `meanFieldFlow_unique`
the attention step *is* the linear pushforward -- the Appendix-B gated machinery (M4) transfers
unchanged to this interface.
-/

namespace MeasureToMeasure.Foundations

open MeasureTheory
open scoped RealInnerProductSpace Classical

variable {d : ℕ}

/-- Coordinatewise ReLU on `Eucl d` (the paper's `(·)₊` applied to `U x + b`). Basis-dependent by
design: the perceptron acts coordinatewise in the ambient basis. -/
noncomputable def reluVec (x : Eucl d) : Eucl d := WithLp.toLp 2 fun i => max 0 (x i)

/-- The measure-valued softmax (self-attention) average `A_B[μ](x)` of eq. (1.2)/(p. 3):
the Gibbs average of `z` under the kernel `e^{⟪Bx, z⟫}` against `μ`. Junk (`0`-denominator gives
the zero vector via `(0 : ℝ)⁻¹ • ⋯ = 0`-free convention: `(∫ ⋯)⁻¹` of a vanishing integral is
`0⁻¹ = 0`... in fact for a probability measure on the sphere the integrand is positive, bounded
and continuous, so the denominator is strictly positive and the value is the genuine average. -/
noncomputable def attnAvg (B : Eucl d →L[ℝ] Eucl d) (μ : Measure (Eucl d)) (x : Eucl d) :
    Eucl d :=
  (∫ z, Real.exp ⟪B x, z⟫ ∂μ)⁻¹ • ∫ z, Real.exp ⟪B x, z⟫ • z ∂μ

/-- One constant-in-time Transformer block: the paper's parameters `θ = (V, B, W, U, b)` (four
`d × d` matrices, here continuous linear endomorphisms, and a bias vector) together with the
duration of the constant piece. A piecewise-constant schedule is a `List (AttnParams d)`. -/
structure AttnParams (d : ℕ) where
  /-- The value matrix multiplying the attention average. -/
  V : Eucl d →L[ℝ] Eucl d
  /-- The query-key matrix inside the attention kernel (inverse temperature absorbed). -/
  B : Eucl d →L[ℝ] Eucl d
  /-- The perceptron outer matrix. -/
  W : Eucl d →L[ℝ] Eucl d
  /-- The perceptron inner matrix. -/
  U : Eucl d →L[ℝ] Eucl d
  /-- The perceptron bias. -/
  b : Eucl d
  /-- The duration of this constant piece. -/
  duration : ℝ
  /-- Durations are nonnegative. -/
  duration_nonneg : 0 ≤ duration

/-- The paper's velocity field (1.2) of one block, at the *current* measure `μ`:
`P_x^⊥ (V (A_B[μ] x) + W (U x + b)₊)`. -/
noncomputable def AttnParams.field (p : AttnParams d) (μ : Measure (Eucl d)) (x : Eucl d) :
    Eucl d :=
  tangentialProjector x (p.V (attnAvg p.B μ x) + p.W (reluVec (p.U x + p.b)))

/-- With `B = 0` the attention kernel is constant `1`, so the softmax average of a probability
measure collapses to the plain barycenter `∫ z ∂μ` (the paper's eq. (3.1) reduction). -/
theorem attnAvg_zero_left (μ : Measure (Eucl d)) [IsProbabilityMeasure μ] (x : Eucl d) :
    attnAvg 0 μ x = ∫ z, z ∂μ := by
  simp [attnAvg]

/-- With `V = 0` the field is measure-independent: it is the pure perceptron field
`P_x^⊥ (W (U x + b)₊)` of eq. (4.1)/(B.1). This is the entry point of the planned bridge to the
linear `Block` flows of `Foundations/GatedBlock.lean`. -/
theorem AttnParams.field_of_V_eq_zero (p : AttnParams d) (hV : p.V = 0)
    (μ : Measure (Eucl d)) (x : Eucl d) :
    p.field μ x = tangentialProjector x (p.W (reluVec (p.U x + p.b))) := by
  simp [AttnParams.field, hV]

/-- A mean-field flow of one block from the initial measure `μ₀`: the characteristics of the
self-referential field `v[μ(t)]` with `μ(t) = (Φ_t)_# μ₀`. The regularity clauses (measurable,
Lipschitz, sphere bijection) are the ones the paper's flow map `φ^t` carries (eq. (B.2):
"Lipschitz-continuous, invertible `φ^t : 𝕊^{d-1} → 𝕊^{d-1}`") and are what the downstream
assemblies consume. -/
structure IsMeanFieldFlow (p : AttnParams d) (μ₀ : Measure (Eucl d))
    (Φ : ℝ → Eucl d → Eucl d) : Prop where
  /-- The flow starts at the identity. -/
  init : Φ 0 = id
  /-- Each time slice is measurable. -/
  measurable : ∀ t ∈ Set.Icc 0 p.duration, Measurable (Φ t)
  /-- The time slices are uniformly Lipschitz. -/
  lipschitz : ∃ L : NNReal, ∀ t ∈ Set.Icc 0 p.duration, LipschitzWith L (Φ t)
  /-- Each time slice restricts to a bijection of the sphere. -/
  sphere_bijOn : ∀ t ∈ Set.Icc 0 p.duration, Set.BijOn (Φ t) (sphere d) (sphere d)
  /-- On the sphere, the trajectories solve the mean-field characteristic ODE: the velocity at
  time `t` is the field evaluated at the *current* pushforward measure `(Φ_t)_# μ₀`. -/
  deriv : ∀ x ∈ sphere d, ∀ t ∈ Set.Icc 0 p.duration,
    HasDerivAt (fun s => Φ s x) (p.field (μ₀.map (Φ t)) (Φ t x)) t

/-- **Well-posedness of the self-attention mean-field flow (existence).** For every Transformer
block and every sphere-supported probability datum there is a mean-field flow. AXIOM
(`math.axiomatised`): this is the McKean-Vlasov well-posedness on the sphere underlying the
paper's eq. (1.3) ("the unique solution `μ ∈ C⁰([0,T]; P(𝕊^{d-1}))`", Theorem 1.1) -- the field
is Lipschitz in `x` and (by the bounded-Lipschitz kernel) Lipschitz in `μ` for `W₂`, so a
Picard-Lindelöf iteration on the product of the point and measure variables converges; Mathlib
`v4.31.0` has no mean-field ODE theory to express this. The measure-independent case (`V = 0`)
is *proved* in `Foundations/FlowMap.lean` (milestone M3); this axiom is the genuinely nonlinear
remainder (M3b). -/
axiom exists_meanFieldFlow (p : AttnParams d) (μ₀ : Measure (Eucl d))
    [IsProbabilityMeasure μ₀] (hs : μ₀ (sphere d)ᶜ = 0) :
    ∃ Φ : ℝ → Eucl d → Eucl d, IsMeanFieldFlow p μ₀ Φ

/-- **Well-posedness of the self-attention mean-field flow (uniqueness on the sphere).** Two
mean-field flows of the same block and datum agree on the sphere throughout the block's duration.
AXIOM (`math.axiomatised`): the uniqueness half of the same McKean-Vlasov well-posedness (a
Grönwall argument in the point and `W₂` variables jointly). It pins the mean-field flow of a
measure-independent block to the linear `Block` flow, which is what transfers the Appendix-B
gated results to this interface. -/
axiom meanFieldFlow_unique {p : AttnParams d} {μ₀ : Measure (Eucl d)}
    {Φ Ψ : ℝ → Eucl d → Eucl d}
    (hΦ : IsMeanFieldFlow p μ₀ Φ) (hΨ : IsMeanFieldFlow p μ₀ Ψ) :
    ∀ t ∈ Set.Icc 0 p.duration, ∀ x ∈ sphere d, Φ t x = Ψ t x

/-- A piecewise-constant Transformer schedule: the list of constant blocks. -/
abbrev AttnSchedule (d : ℕ) := List (AttnParams d)

namespace AttnSchedule

/-- The number of constant pieces of a schedule. Convention: `switches` counts *pieces* (as the
linear `Params` does; a single block has `switches = 1`). The paper counts sometimes pieces
(Prop. 4.2: "6 switches" for a 6-piece schedule) and sometimes discontinuities (Lemma 3.2:
"one switch" for a 2-piece schedule); we use pieces uniformly. -/
def switches (θ : AttnSchedule d) : ℕ := θ.length

@[simp] theorem switches_nil : switches ([] : AttnSchedule d) = 0 := rfl

@[simp] theorem switches_append (θ ψ : AttnSchedule d) :
    switches (θ ++ ψ) = switches θ + switches ψ := List.length_append ..

/-- The total duration of a schedule: the sum of its pieces' durations. The paper's horizon `T`
is the total duration of the piecewise-constant parameter path `θ : [0, T] → Θ`. -/
def durationSum (θ : AttnSchedule d) : ℝ := (θ.map AttnParams.duration).sum

@[simp] theorem durationSum_nil : durationSum ([] : AttnSchedule d) = 0 := rfl

@[simp] theorem durationSum_append (θ ψ : AttnSchedule d) :
    durationSum (θ ++ ψ) = durationSum θ + durationSum ψ := by
  simp [durationSum]

/-- Durations are nonnegative, hence so is the total. -/
theorem durationSum_nonneg (θ : AttnSchedule d) : 0 ≤ durationSum θ := by
  induction θ with
  | nil => simp
  | cons p rest ih =>
    have h : durationSum (p :: rest) = p.duration + durationSum rest := by simp [durationSum]
    rw [h]
    exact add_nonneg p.duration_nonneg ih

end AttnSchedule

/-- One block step of the measure-level solution operator: push `μ` forward along the block's
mean-field flow at its duration. Junk branch: off sphere-supported probability data the step is
the identity (every downstream statement carries the sphere-probability hypotheses). -/
noncomputable def attnStep (p : AttnParams d) (μ : Measure (Eucl d)) : Measure (Eucl d) :=
  if h : IsProbabilityMeasure μ ∧ μ (sphere d)ᶜ = 0 then
    μ.map ((@exists_meanFieldFlow d p μ h.1 h.2).choose p.duration)
  else μ

/-- The solution operator of a schedule: fold the per-block steps left-to-right (run the first
block first). -/
noncomputable def attnMeasureFlow (θ : AttnSchedule d) (μ : Measure (Eucl d)) :
    Measure (Eucl d) :=
  θ.foldl (fun ν p => attnStep p ν) μ

@[simp] theorem attnMeasureFlow_nil (μ : Measure (Eucl d)) :
    attnMeasureFlow ([] : AttnSchedule d) μ = μ := rfl

/-- Composition of schedules is concatenation: running `θ ++ ψ` is running `θ`, then `ψ`. -/
theorem attnMeasureFlow_append (θ ψ : AttnSchedule d) (μ : Measure (Eucl d)) :
    attnMeasureFlow (θ ++ ψ) μ = attnMeasureFlow ψ (attnMeasureFlow θ μ) :=
  List.foldl_append ..

/-- One step preserves probability (on sphere-supported probability data). -/
theorem isProbabilityMeasure_attnStep (p : AttnParams d) (μ : Measure (Eucl d))
    [IsProbabilityMeasure μ] (hs : μ (sphere d)ᶜ = 0) :
    IsProbabilityMeasure (attnStep p μ) := by
  rw [attnStep, dif_pos ⟨‹IsProbabilityMeasure μ›, hs⟩]
  have hspec := (@exists_meanFieldFlow d p μ ‹_› hs).choose_spec
  have hm := hspec.measurable p.duration ⟨p.duration_nonneg, le_rfl⟩
  exact ⟨by rw [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ]; exact measure_univ⟩

/-- One step preserves sphere support: the flow maps the sphere into itself. -/
theorem attnStep_supportedIn_sphere (p : AttnParams d) (μ : Measure (Eucl d))
    [IsProbabilityMeasure μ] (hs : μ (sphere d)ᶜ = 0) :
    (attnStep p μ) (sphere d)ᶜ = 0 := by
  rw [attnStep, dif_pos ⟨‹IsProbabilityMeasure μ›, hs⟩]
  have hspec := (@exists_meanFieldFlow d p μ ‹_› hs).choose_spec
  have hdur : p.duration ∈ Set.Icc 0 p.duration := ⟨p.duration_nonneg, le_rfl⟩
  have hms : MeasurableSet (sphere d)ᶜ := Metric.isClosed_sphere.measurableSet.compl
  rw [Measure.map_apply (hspec.measurable p.duration hdur) hms]
  refine measure_mono_null (fun x hx => ?_) hs
  simp only [Set.mem_preimage, Set.mem_compl_iff] at hx ⊢
  exact fun hxs => hx ((hspec.sphere_bijOn p.duration hdur).mapsTo hxs)

/-- The solution operator preserves probability and sphere support along the whole schedule. -/
theorem attnMeasureFlow_prob_supportedIn_sphere (θ : AttnSchedule d) :
    ∀ (μ : Measure (Eucl d)), IsProbabilityMeasure μ → μ (sphere d)ᶜ = 0 →
      IsProbabilityMeasure (attnMeasureFlow θ μ) ∧ (attnMeasureFlow θ μ) (sphere d)ᶜ = 0 := by
  induction θ with
  | nil => exact fun μ hμ hs => ⟨hμ, hs⟩
  | cons p rest ih =>
    intro μ hμ hs
    haveI := hμ
    have h1 := isProbabilityMeasure_attnStep p μ hs
    have h2 := attnStep_supportedIn_sphere p μ hs
    simpa [attnMeasureFlow] using ih (attnStep p μ) h1 h2

/-- The solution operator preserves probability (on sphere-supported probability data). -/
theorem isProbabilityMeasure_attnMeasureFlow (θ : AttnSchedule d) (μ : Measure (Eucl d))
    [IsProbabilityMeasure μ] (hs : μ (sphere d)ᶜ = 0) :
    IsProbabilityMeasure (attnMeasureFlow θ μ) :=
  (attnMeasureFlow_prob_supportedIn_sphere θ μ ‹_› hs).1

/-- The solution operator preserves sphere support (on sphere-supported probability data). -/
theorem attnMeasureFlow_supportedIn_sphere (θ : AttnSchedule d) (μ : Measure (Eucl d))
    [IsProbabilityMeasure μ] (hs : μ (sphere d)ᶜ = 0) :
    (attnMeasureFlow θ μ) (sphere d)ᶜ = 0 :=
  (attnMeasureFlow_prob_supportedIn_sphere θ μ ‹_› hs).2

/-! ### The linear bridge: measure-independent blocks realize the mean-field flow

For `V = 0` the field ignores the measure, so the McKean-Vlasov system degenerates to the plain
characteristic ODE that `Foundations/FlowMap.lean` already solves by Picard-Lindelöf. The two
lemmas below make that identification kernel-checked *relative to the well-posedness interface*:
the linear `Block` flow satisfies `IsMeanFieldFlow`, and by `meanFieldFlow_unique` the attention
step of a `V = 0` block IS the linear pushforward. This is what transfers the Appendix-B gated
results (milestone M4, e.g. `gated_twoCap_retention`) to the mean-field layer. -/

/-- A linear `Block` whose field agrees on the sphere with the (measure-independent) perceptron
field of a `V = 0` attention block realizes a mean-field flow of that block, from every initial
measure. The predicate only constrains trajectories on the sphere, which the block flow preserves;
uniform Lipschitzness over the duration comes from the Grönwall spread bound. -/
theorem isMeanFieldFlow_blockFlow (b : Block d) (p : AttnParams d) (hV : p.V = 0)
    (hagree : ∀ y ∈ sphere d, b.field y = tangentialProjector y (p.W (reluVec (p.U y + p.b))))
    (μ₀ : Measure (Eucl d)) :
    IsMeanFieldFlow p μ₀ (fun t => b.blockFlow t) where
  init := b.blockFlow_zero_eq_id
  measurable := fun _ ht => b.measurable_blockFlow ht.1
  lipschitz := by
    refine ⟨(Real.exp (b.lipConst * p.duration)).toNNReal, fun t ht => ?_⟩
    refine (b.lipschitzWith_blockFlow ht.1).weaken ?_
    have hle : b.lipConst * t ≤ b.lipConst * p.duration :=
      mul_le_mul_of_nonneg_left ht.2 b.lipConst.coe_nonneg
    exact Real.toNNReal_mono (Real.exp_le_exp.mpr hle)
  sphere_bijOn := fun t ht => by
    refine ⟨fun x hx => b.blockFlow_mem_sphere hx ht.1, (b.blockFlow_injective t).injOn,
      fun y hy => ⟨b.neg.blockFlow t y, b.neg.blockFlow_mem_sphere hy ht.1, ?_⟩⟩
    rw [b.blockFlow_neg t y, b.blockFlow_add]
    simp
  deriv := fun x hx t ht => by
    rw [p.field_of_V_eq_zero hV, ← hagree _ (b.blockFlow_mem_sphere hx ht.1)]
    exact b.blockCurve_isIntegralCurve x t

/-- **The linear bridge.** The attention step of a `V = 0` block coincides with the linear
pushforward along any `Block` whose field matches on the sphere: the block flow is a mean-field
flow (`isMeanFieldFlow_blockFlow`), uniqueness pins the chosen flow to it on the sphere, and sphere
support upgrades the pointwise agreement to equality of pushforwards. First consumer of
`meanFieldFlow_unique`. -/
theorem attnStep_eq_map_blockFlow (p : AttnParams d) (hV : p.V = 0) (b : Block d)
    (hagree : ∀ y ∈ sphere d, b.field y = tangentialProjector y (p.W (reluVec (p.U y + p.b))))
    (μ₀ : Measure (Eucl d)) [IsProbabilityMeasure μ₀] (hs : μ₀ (sphere d)ᶜ = 0) :
    attnStep p μ₀ = μ₀.map (b.blockFlow p.duration) := by
  rw [attnStep, dif_pos ⟨‹IsProbabilityMeasure μ₀›, hs⟩]
  have hΦ := (@exists_meanFieldFlow d p μ₀ ‹_› hs).choose_spec
  have heq := meanFieldFlow_unique hΦ (isMeanFieldFlow_blockFlow b p hV hagree μ₀)
    p.duration ⟨p.duration_nonneg, le_rfl⟩
  refine Measure.map_congr ?_
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun x hx => ?_) hs
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff] at hx ⊢
  exact fun hxs => hx (heq x hxs)

/-- The singleton-schedule form of the bridge: one `V = 0` piece is the linear block flow. -/
theorem attnMeasureFlow_singleton_eq_map_blockFlow (p : AttnParams d) (hV : p.V = 0)
    (b : Block d)
    (hagree : ∀ y ∈ sphere d, b.field y = tangentialProjector y (p.W (reluVec (p.U y + p.b))))
    (μ₀ : Measure (Eucl d)) [IsProbabilityMeasure μ₀] (hs : μ₀ (sphere d)ᶜ = 0) :
    attnMeasureFlow [p] μ₀ = μ₀.map (b.blockFlow p.duration) :=
  attnStep_eq_map_blockFlow p hV b hagree μ₀ hs

end MeasureToMeasure.Foundations
