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
* `AttnSchedule`, `switches`, `durationSum` -- a piecewise-constant schedule and its bookkeeping;
  composition over `++` is definitional.
* `isMeanFieldFlow_blockFlow` -- for a block with `V = 0` the field is measure-independent
  (`AttnParams.field_of_V_eq_zero`); any linear `Block` whose field agrees with it on the sphere
  realizes a mean-field flow.

**`exists_meanFieldFlow`, `attnStep`, `attnMeasureFlow`, and the linear bridge
(`attnStep_eq_map_blockFlow`) now live in `Foundations/AttnStepExistence.lean`**, downstream of
this file: `exists_meanFieldFlow` was the sole remaining axiom here (EXISTENCE of the McKean-Vlasov
characteristic flow on the sphere for sphere-supported probability data), now `math.machine-checked`
via a genuine Picard iteration in the joint (point, `W₁`) variable (M3b existence campaign). Its
companion `meanFieldFlow_unique` (UNIQUENESS) is a THEOREM (`MeanFieldWellPosed.meanFieldFlow_unique`),
machine-checked via the measure-averaged Grönwall route. The proof needs the whole M3b chain, which
itself needs `AttnParams`/`IsMeanFieldFlow` from here, so `attnStep`/`attnMeasureFlow` (which consume
the theorem) had to relocate downstream rather than stay in this file -- see
`AttnStepExistence.lean`'s module docstring for the full story.
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

-- `exists_meanFieldFlow` (well-posedness/existence of the self-attention mean-field flow) was the
-- sole remaining axiom here; it now lives, discharged as a theorem, in `AttnStepExistence.lean` --
-- see the module docstring above and that file's docstring for the full story.

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


/-- A sphere-supported probability measure sees a nonempty sphere. Used by
`AttnStepExistence.attnStep_exists_map` (the transport-map extraction, relocated there along with
`attnStep`/`attnMeasureFlow` since it needs the genuine `exists_meanFieldFlow` theorem). -/
theorem sphere_nonempty_of_supported (μ : Measure (Eucl d)) [IsProbabilityMeasure μ]
    (hs : μ (sphere d)ᶜ = 0) : (sphere d).Nonempty := by
  rcases Set.eq_empty_or_nonempty (sphere d) with hempty | hne
  · exfalso
    have huniv : (sphere d)ᶜ = Set.univ := by rw [hempty, Set.compl_empty]
    have : μ Set.univ = 0 := huniv ▸ hs
    simpa [this] using (measure_univ (μ := μ))
  · exact hne

end MeasureToMeasure.Foundations
