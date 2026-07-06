import MeasureToMeasure.Foundations.MeanFieldWellPosed
import MeasureToMeasure.Foundations.SphereFlow
import MeasureToMeasure.Foundations.BallProjection

/-!
# Frozen-field bounds for mean-field existence (M3b, leaf E2-groundwork)

Groundwork toward discharging `exists_meanFieldFlow` (M3b existence). The existence proof solves the
characteristic ODE `ẋ = field(ν, x)` for a *frozen* sphere-supported measure `ν` (inside a Picard
iteration over the measure trajectory), and keeps the solution on the sphere via
`SphereFlow.sphere_invariant`. Applying that machinery to the attention field needs two facts about
the frozen field, both assembled here from the banked moduli of `MeanFieldWellPosed`:

* the field is **tangent** on the sphere — its radial component is `⟪x, rawField⟫·(1 - ‖x‖²)`, which
  vanishes on `‖x‖ = 1` (`inner_field_left`, from `SphereFlow.inner_tangentialProjector_left`); this
  is the identity `sphere_invariant`'s Grönwall consumes;
* the raw (pre-projection) field is **uniformly bounded** on the sphere by an explicit block constant
  (`norm_rawField_le_onSphere`, from `norm_attnAvg_le` + `norm_reluVec_le`), giving the radial-drift
  bound `sphere_invariant` needs.

These are the sphere-side inputs; the remaining existence work is the globally-Lipschitz bounded
*extension* of the field off the sphere (so Mathlib's `IsPicardLindelof.of_time_independent` applies,
as for the linear `blockFlow`), then the Picard fixed point over the measure trajectory.

**Leaf E2a-2 (this file's second half): the ball-tamed raw field is globally nice.** The softmax
moduli of `MeanFieldWellPosed` (`norm_attnAvg_le`, `attnAvg_sub_le_of_norm_le`) hold only on the
closed unit ball `‖x‖ ≤ 1`; off it the Gibbs kernel `e^{⟪Bx,z⟫}` is unbounded. Precomposing the raw
field with the `1`-Lipschitz ball retraction `ballProj` (leaf E2a-1), which always lands in that ball
and fixes it, turns those on-ball estimates into **global** ones with the *same* constants:
`rawFieldBall p ν := rawField p ν ∘ ballProj` is globally bounded (`norm_rawFieldBall_le`) and
globally Lipschitz (`norm_rawFieldBall_sub_le`), and agrees with `rawField` on the ball (hence on the
sphere, `rawFieldBall_eq_rawField_of_norm_le_one`). This is the softmax+perceptron half of the
globally-Lipschitz field extension; the outer tangential projector `P_x^⊥` — quadratic in the base
point, so still not globally Lipschitz — is localized by `normCutoff` when the `Block` is assembled
(leaf E2a-3, via `GatedBlock.lipschitzWith_smul_of_vanishing`).
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace MeasureToMeasure.Foundations

variable {d : ℕ}

/-- The raw (pre-tangential-projection) attention velocity of a block at measure `ν`:
`V · A_B[ν](x) + W · (U x + b)₊`. The field is its tangential projection,
`p.field ν x = P_x^⊥ (rawField p ν x)`. -/
noncomputable def rawField (p : AttnParams d) (ν : Measure (Eucl d)) (x : Eucl d) : Eucl d :=
  p.V (attnAvg p.B ν x) + p.W (reluVec (p.U x + p.b))

theorem field_eq_tangentialProjector_rawField (p : AttnParams d) (ν : Measure (Eucl d))
    (x : Eucl d) : p.field ν x = tangentialProjector x (rawField p ν x) := rfl

/-- **Tangency / radial identity.** The radial component of the field is `⟪x, rawField⟫·(1 - ‖x‖²)`,
so on the sphere (`‖x‖ = 1`) the field is tangent. This is exactly the `hrad` hypothesis of
`SphereFlow.sphere_invariant` (with raw drift `⟪x, rawField p ν x⟫`). -/
theorem inner_field_left (p : AttnParams d) (ν : Measure (Eucl d)) (x : Eucl d) :
    ⟪x, p.field ν x⟫ = ⟪x, rawField p ν x⟫ * (1 - ‖x‖ ^ 2) := by
  rw [field_eq_tangentialProjector_rawField, inner_tangentialProjector_left]

/-- **Uniform bound on the raw field over the sphere.** For a sphere-supported probability measure
`ν`, the raw attention velocity is bounded on the sphere by the explicit block constant
`‖V‖·e^{2‖B‖} + ‖W‖·(‖U‖ + ‖b‖)`: the attention average is bounded by `e^{2‖B‖}` (`norm_attnAvg_le`)
and the perceptron term by `‖W‖·(‖U‖ + ‖b‖)` (`reluVec` is nonexpansive, `‖x‖ = 1`). -/
theorem norm_rawField_le_onSphere (p : AttnParams d) (ν : Measure (Eucl d)) [IsProbabilityMeasure ν]
    (hν : ν (sphere d)ᶜ = 0) {x : Eucl d} (hx : x ∈ sphere d) :
    ‖rawField p ν x‖ ≤ ‖p.V‖ * Real.exp (2 * ‖p.B‖) + ‖p.W‖ * (‖p.U‖ + ‖p.b‖) := by
  have hx1 : ‖x‖ = 1 := norm_eq_one_of_mem_sphere hx
  -- attention term: ‖V (A_B[ν] x)‖ ≤ ‖V‖ · e^{2‖B‖}
  have hV : ‖p.V (attnAvg p.B ν x)‖ ≤ ‖p.V‖ * Real.exp (2 * ‖p.B‖) := by
    refine (p.V.le_opNorm _).trans ?_
    exact mul_le_mul_of_nonneg_left (norm_attnAvg_le p.B hν (le_of_eq hx1)) (norm_nonneg _)
  -- perceptron term: ‖W ((U x + b)₊)‖ ≤ ‖W‖ · (‖U‖ + ‖b‖)
  have hW : ‖p.W (reluVec (p.U x + p.b))‖ ≤ ‖p.W‖ * (‖p.U‖ + ‖p.b‖) := by
    refine (p.W.le_opNorm _).trans ?_
    refine mul_le_mul_of_nonneg_left ((norm_reluVec_le _).trans ?_) (norm_nonneg _)
    calc ‖p.U x + p.b‖ ≤ ‖p.U x‖ + ‖p.b‖ := norm_add_le _ _
      _ ≤ ‖p.U‖ * ‖x‖ + ‖p.b‖ := by gcongr; exact p.U.le_opNorm x
      _ = ‖p.U‖ + ‖p.b‖ := by rw [hx1, mul_one]
  calc ‖rawField p ν x‖ ≤ ‖p.V (attnAvg p.B ν x)‖ + ‖p.W (reluVec (p.U x + p.b))‖ :=
        norm_add_le _ _
    _ ≤ ‖p.V‖ * Real.exp (2 * ‖p.B‖) + ‖p.W‖ * (‖p.U‖ + ‖p.b‖) := by gcongr

/-! ## The ball-tamed raw field (leaf E2a-2)

The two `rawField` bounds above are stated on the sphere, but their proofs only use `‖x‖ ≤ 1`; the
softmax moduli they invoke are on-ball facts. We record the ball-level versions and then precompose
with the retraction `ballProj` (leaf E2a-1) to make the raw field globally bounded and Lipschitz. -/

/-- **Uniform bound on the raw field over the closed unit ball.** The on-sphere bound
(`norm_rawField_le_onSphere`) needed only `‖x‖ ≤ 1`, so it holds on the whole ball. -/
theorem norm_rawField_le_of_norm_le_one (p : AttnParams d) (ν : Measure (Eucl d))
    [IsProbabilityMeasure ν] (hν : ν (sphere d)ᶜ = 0) {x : Eucl d} (hx : ‖x‖ ≤ 1) :
    ‖rawField p ν x‖ ≤ ‖p.V‖ * Real.exp (2 * ‖p.B‖) + ‖p.W‖ * (‖p.U‖ + ‖p.b‖) := by
  have hV : ‖p.V (attnAvg p.B ν x)‖ ≤ ‖p.V‖ * Real.exp (2 * ‖p.B‖) :=
    (p.V.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_attnAvg_le p.B hν hx) (norm_nonneg _))
  have hW : ‖p.W (reluVec (p.U x + p.b))‖ ≤ ‖p.W‖ * (‖p.U‖ + ‖p.b‖) := by
    refine (p.W.le_opNorm _).trans ?_
    refine mul_le_mul_of_nonneg_left ((norm_reluVec_le _).trans ?_) (norm_nonneg _)
    calc ‖p.U x + p.b‖ ≤ ‖p.U x‖ + ‖p.b‖ := norm_add_le _ _
      _ ≤ ‖p.U‖ * ‖x‖ + ‖p.b‖ := by gcongr; exact p.U.le_opNorm x
      _ ≤ ‖p.U‖ + ‖p.b‖ := by
          have : ‖p.U‖ * ‖x‖ ≤ ‖p.U‖ := by
            calc ‖p.U‖ * ‖x‖ ≤ ‖p.U‖ * 1 := by gcongr
              _ = ‖p.U‖ := mul_one _
          linarith
  calc ‖rawField p ν x‖ ≤ ‖p.V (attnAvg p.B ν x)‖ + ‖p.W (reluVec (p.U x + p.b))‖ :=
        norm_add_le _ _
    _ ≤ ‖p.V‖ * Real.exp (2 * ‖p.B‖) + ‖p.W‖ * (‖p.U‖ + ‖p.b‖) := by gcongr

/-- **Point modulus of the raw field on the closed unit ball.** For a sphere-supported probability
measure and points of the unit ball, the raw (pre-projection) field is Lipschitz with the same
constant that drives the field's on-sphere point modulus: the attention point modulus
(`attnAvg_sub_le_of_norm_le`) for the `V`-term, the nonexpansive coordinatewise ReLU
(`norm_reluVec_sub_le`) for the perceptron term. (This is the `‖a_x - a_y‖` core of
`norm_field_sub_point_le`, without the projector's own base-point dependence.) -/
theorem norm_rawField_sub_le_of_norm_le_one (p : AttnParams d) (ν : Measure (Eucl d))
    [IsProbabilityMeasure ν] (hν : ν (sphere d)ᶜ = 0) {x y : Eucl d} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖rawField p ν x - rawField p ν y‖ ≤
      (‖p.V‖ * (2 * ‖p.B‖ * Real.exp (4 * ‖p.B‖)) + ‖p.W‖ * ‖p.U‖) * ‖x - y‖ := by
  have e1 : rawField p ν x - rawField p ν y = p.V (attnAvg p.B ν x - attnAvg p.B ν y)
      + p.W (reluVec (p.U x + p.b) - reluVec (p.U y + p.b)) := by
    simp only [rawField, map_sub]; abel
  have eU : (p.U x + p.b) - (p.U y + p.b) = p.U (x - y) := by rw [map_sub]; abel
  rw [e1]
  calc ‖p.V (attnAvg p.B ν x - attnAvg p.B ν y)
          + p.W (reluVec (p.U x + p.b) - reluVec (p.U y + p.b))‖
      ≤ ‖p.V (attnAvg p.B ν x - attnAvg p.B ν y)‖
          + ‖p.W (reluVec (p.U x + p.b) - reluVec (p.U y + p.b))‖ := norm_add_le _ _
    _ ≤ ‖p.V‖ * ‖attnAvg p.B ν x - attnAvg p.B ν y‖
          + ‖p.W‖ * ‖reluVec (p.U x + p.b) - reluVec (p.U y + p.b)‖ :=
        add_le_add (p.V.le_opNorm _) (p.W.le_opNorm _)
    _ ≤ ‖p.V‖ * (2 * ‖p.B‖ * Real.exp (4 * ‖p.B‖) * ‖x - y‖) + ‖p.W‖ * ‖p.U (x - y)‖ := by
        gcongr
        · exact attnAvg_sub_le_of_norm_le p.B hν hx hy
        · rw [← eU]; exact norm_reluVec_sub_le _ _
    _ ≤ ‖p.V‖ * (2 * ‖p.B‖ * Real.exp (4 * ‖p.B‖) * ‖x - y‖) + ‖p.W‖ * (‖p.U‖ * ‖x - y‖) := by
        gcongr; exact p.U.le_opNorm _
    _ = (‖p.V‖ * (2 * ‖p.B‖ * Real.exp (4 * ‖p.B‖)) + ‖p.W‖ * ‖p.U‖) * ‖x - y‖ := by ring

/-- The raw attention velocity **precomposed with the ball retraction** `ballProj` (leaf E2a-1). Since
`ballProj` always lands in the closed unit ball, where the softmax moduli hold, this is globally
bounded and globally Lipschitz — unlike `rawField`, whose bounds hold only on the ball. -/
noncomputable def rawFieldBall (p : AttnParams d) (ν : Measure (Eucl d)) (x : Eucl d) : Eucl d :=
  rawField p ν (ballProj x)

/-- On the closed unit ball (in particular on the sphere) `ballProj` is the identity, so `rawFieldBall`
agrees with `rawField`. -/
theorem rawFieldBall_eq_rawField_of_norm_le_one (p : AttnParams d) (ν : Measure (Eucl d)) {x : Eucl d}
    (hx : ‖x‖ ≤ 1) : rawFieldBall p ν x = rawField p ν x := by
  rw [rawFieldBall, ballProj_eq_self hx]

/-- **Global bound on the ball-tamed raw field:** the on-ball bound at `ballProj x` (always in the
ball). -/
theorem norm_rawFieldBall_le (p : AttnParams d) (ν : Measure (Eucl d)) [IsProbabilityMeasure ν]
    (hν : ν (sphere d)ᶜ = 0) (x : Eucl d) :
    ‖rawFieldBall p ν x‖ ≤ ‖p.V‖ * Real.exp (2 * ‖p.B‖) + ‖p.W‖ * (‖p.U‖ + ‖p.b‖) :=
  norm_rawField_le_of_norm_le_one p ν hν (norm_ballProj_le x)

/-- **The ball-tamed raw field is globally Lipschitz:** the on-ball point modulus at `ballProj x`,
`ballProj y` (both in the ball) composed with `ballProj`'s `1`-Lipschitzness (leaf E2a-1). Its global
Lipschitz constant is the same `L = ‖V‖·2‖B‖e^{4‖B‖} + ‖W‖·‖U‖` that drives the field's on-sphere point
modulus. -/
theorem norm_rawFieldBall_sub_le (p : AttnParams d) (ν : Measure (Eucl d)) [IsProbabilityMeasure ν]
    (hν : ν (sphere d)ᶜ = 0) (x y : Eucl d) :
    ‖rawFieldBall p ν x - rawFieldBall p ν y‖ ≤
      (‖p.V‖ * (2 * ‖p.B‖ * Real.exp (4 * ‖p.B‖)) + ‖p.W‖ * ‖p.U‖) * ‖x - y‖ := by
  have hbxy : ‖ballProj x - ballProj y‖ ≤ ‖x - y‖ := by
    have h := (lipschitzWith_ballProj (E := Eucl d)).dist_le_mul x y
    rwa [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at h
  have hC : (0 : ℝ) ≤ ‖p.V‖ * (2 * ‖p.B‖ * Real.exp (4 * ‖p.B‖)) + ‖p.W‖ * ‖p.U‖ := by positivity
  calc ‖rawFieldBall p ν x - rawFieldBall p ν y‖
      ≤ (‖p.V‖ * (2 * ‖p.B‖ * Real.exp (4 * ‖p.B‖)) + ‖p.W‖ * ‖p.U‖) * ‖ballProj x - ballProj y‖ :=
        norm_rawField_sub_le_of_norm_le_one p ν hν (norm_ballProj_le x) (norm_ballProj_le y)
    _ ≤ (‖p.V‖ * (2 * ‖p.B‖ * Real.exp (4 * ‖p.B‖)) + ‖p.W‖ * ‖p.U‖) * ‖x - y‖ :=
        mul_le_mul_of_nonneg_left hbxy hC

end MeasureToMeasure.Foundations
