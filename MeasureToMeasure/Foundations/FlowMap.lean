import MeasureToMeasure.Foundations.SphereFlow
import Mathlib.Analysis.ODE.PicardLindelof

/-!
# The mean-field flow map (M3): the per-block characteristic flow

The continuity equation (1.2)-(1.3) transports mass along the characteristics `ẋ = V(x)` of a
layer-normalized velocity field. This file builds the flow map `Φ_θ^t` that `Axioms/*` currently
axiomatize, discharging the M3 milestone at its faithful primitive point.

The key modeling choice is what a **block** is. Rather than fixing one algebraic velocity field, a
`Block` bundles the *well-posedness data* the flow actually needs: a **globally-Lipschitz** velocity
field that is **radially tangent** (`⟪x, V x⟫ = gate x · (‖x‖² − 1)`, so `V` is tangent on the unit
sphere and its flow preserves the sphere), plus a nonnegative **duration**. The paper's per-block
fields -- the ReLU-gated projected field `P_x^⊥((cos R − ⟪z,x⟫)_+ • ω)` (B.5) and the barycenter
field `P_x^⊥(⟪𝔼_μ[x],α⟫ • α)` (B.9) -- are *instances* of a `Block` (after a cutoff off the sphere
makes them globally Lipschitz; the quadratic projector is only locally Lipschitz). Isolating the
well-posedness this way is what lets the flow map, its Lipschitz/bijectivity/semigroup/parked laws,
and the schedule algebra all be *proved* from the autonomous-field lemmas in `SphereFlow.lean` plus
Mathlib's `IsPicardLindelof.of_time_independent`.
-/

namespace MeasureToMeasure

open scoped RealInnerProductSpace NNReal
open Set

variable {d : ℕ}

/-- A **well-posed velocity block** for the characteristic flow: a globally-Lipschitz, radially
tangent velocity field on `ℝ^d` together with a nonnegative time duration. Concrete (a `structure`,
not an axiom), so `Params := List (Block d)` makes the schedule algebra -- composition as
concatenation, identity as the empty list, reversal as `List.reverse` -- provable rather than
assumed. -/
structure Block (d : ℕ) where
  /-- the velocity field, taken already globally Lipschitz (e.g. the paper's field cut off away from
  the sphere, where the raw quadratic projector would only be locally Lipschitz). -/
  field : Eucl d → Eucl d
  /-- a global Lipschitz constant for `field`. -/
  lipConst : ℝ≥0
  /-- `field` is globally `lipConst`-Lipschitz -- the hypothesis Picard-Lindelöf needs. -/
  lipschitz : LipschitzWith lipConst field
  /-- a global bound on `field`. The paper's cutoff field is bounded; global boundedness is what makes
  Picard-Lindelöf existence hold on the *whole* interval `[0, dur]` (the ball radius can be taken
  `bound · dur` larger without the field's bound growing with it). -/
  bound : ℝ≥0
  /-- `field` is globally bounded by `bound`. -/
  field_le : ∀ x, ‖field x‖ ≤ bound
  /-- the radial **gate** `c(x)`: `⟪x, field x⟫ = c(x) · (‖x‖² − 1)`. On the sphere this is `0`, i.e.
  `field` is tangent; off the sphere `c` measures the radial drift the Grönwall argument controls. -/
  gate : Eucl d → ℝ
  /-- a uniform bound on twice the gate, feeding the Grönwall sphere-invariance estimate. -/
  gateBound : ℝ
  /-- the uniform gate bound holds everywhere. -/
  gate_le : ∀ x, |2 * gate x| ≤ gateBound
  /-- the radial-tangency identity that makes the flow preserve the sphere. -/
  radial : ∀ x, (⟪x, field x⟫ : ℝ) = gate x * (‖x‖ ^ 2 - 1)
  /-- the block's time duration. -/
  dur : ℝ
  /-- durations are nonnegative. -/
  dur_nonneg : 0 ≤ dur

/-- A **parameter schedule** is a finite list of blocks. Concatenation is composition of flows, the
empty list is the identity schedule, and the list length is the switch (depth) count. -/
abbrev Params (d : ℕ) : Type := List (Block d)

/-- The number of parameter switches of a schedule: its block count (Section 1.4.3 depth proxy). -/
def switches (θ : Params d) : ℕ := θ.length

/-!
## Per-block existence (Picard-Lindelöf)

The block's autonomous field is globally bounded and globally Lipschitz, so Picard-Lindelöf holds on
the *whole* symmetric interval `[-T, T]` around any point: taking the ball radius `bound·T + r`, the
global bound `‖field‖ ≤ bound` keeps the well-posedness constant from growing with the radius, so the
interval condition `L·T ≤ a - r` is met with equality. This is what sidesteps the missing global-
existence continuation -- boundedness on a fixed time interval is enough.
-/

/-- **Picard-Lindelöf for a block's field** on `[-T, T]` around `x₀`, for any radius `r`. Global
boundedness (`field_le`) and global Lipschitzness supply the three `of_time_independent` hypotheses;
the interval condition holds with equality by the choice `a = bound·T + r`. -/
theorem Block.isPicardLindelof (b : Block d) (x₀ : Eucl d) (T r : ℝ≥0) :
    IsPicardLindelof (fun _ => b.field)
      (⟨0, Set.mem_Icc.mpr ⟨neg_nonpos.mpr T.coe_nonneg, T.coe_nonneg⟩⟩ : Set.Icc (-(T : ℝ)) T)
      x₀ (b.bound * T + r) r b.bound b.lipConst := by
  apply IsPicardLindelof.of_time_independent
  · intro x _; exact b.field_le x
  · exact b.lipschitz.lipschitzOnWith
  · have hmax : max ((T : ℝ) - 0) (0 - -(T : ℝ)) = (T : ℝ) := by
      rw [sub_zero, zero_sub, neg_neg, max_self]
    rw [hmax]
    push_cast
    ring_nf
    rfl

/-- **Interval integral curve through `x₀`.** For any `T ≥ 0` there is a curve `α` with `α 0 = x₀`
that solves `ẋ = field x` on `[-T, T]`. The value at the block's duration is one point-flow step. -/
theorem Block.exists_integralCurveOn (b : Block d) (x₀ : Eucl d) (T : ℝ≥0) :
    ∃ α : ℝ → Eucl d, α 0 = x₀ ∧
      ∀ t ∈ Set.Icc (-(T : ℝ)) T, HasDerivWithinAt α (b.field (α t)) (Set.Icc (-(T : ℝ)) T) t := by
  have hx : x₀ ∈ Metric.closedBall x₀ ((0 : ℝ≥0) : ℝ) := by simp
  obtain ⟨α, hα0, hαderiv⟩ :=
    (b.isPicardLindelof x₀ T 0).exists_eq_forall_mem_Icc_hasDerivWithinAt hx
  exact ⟨α, hα0, hαderiv⟩

end MeasureToMeasure
