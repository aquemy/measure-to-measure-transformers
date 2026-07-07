import MeasureToMeasure.Foundations.Projector
import MeasureToMeasure.Foundations.GeodesicDistance
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Leaf L4: the gradient of geodesic distance (eq. after 4.4)

The gradient flow (4.4)-(4.6) uses `∇₁ d_g(x, ω) = - P_x^⊥ ω / √(1 - ⟪x, ω⟫²)`. We kernel-check the
two facts behind this:

* the derivative of `t ↦ d_g(x(t), ω)` along a path is `-(1/√(1-⟪x,ω⟫²)) · ⟪x'(t), ω⟫`
  (chain rule for `arccos∘⟪·,ω⟫`);
* on the sphere, for a tangent velocity (`⟪x', x⟫ = 0`) one has `⟪x', ω⟫ = ⟪x', P_x^⊥ ω⟫`, so the
  derivative is `⟪x', -(1/√(1-⟪x,ω⟫²)) • P_x^⊥ ω⟫`, exhibiting `-P_x^⊥ ω / √(1-⟪x,ω⟫²)` as the
  Riemannian (tangential) gradient.
-/

namespace MeasureToMeasure.Leaves

open scoped RealInnerProductSpace
open MeasureToMeasure

variable {d : ℕ}

/-- L4 (derivative of geodesic distance along a path): the chain rule for `arccos∘⟪·, ω⟫`. -/
theorem geodesicDist_hasDerivAt {x : ℝ → Eucl d} {ω : Eucl d} {t : ℝ} {x' : Eucl d}
    (hx : HasDerivAt x x' t) (h1 : (⟪x t, ω⟫ : ℝ) ≠ -1) (h2 : (⟪x t, ω⟫ : ℝ) ≠ 1) :
    HasDerivAt (fun s => geodesicDist (x s) ω)
      (-(1 / Real.sqrt (1 - (⟪x t, ω⟫ : ℝ) ^ 2)) * ⟪x', ω⟫) t := by
  have hinner : HasDerivAt (fun s => (⟪x s, ω⟫ : ℝ)) (⟪x', ω⟫) t := by
    have h := hx.inner ℝ (hasDerivAt_const t ω)
    simpa using h
  have h := (Real.hasDerivAt_arccos h1 h2).comp t hinner
  simpa only [geodesicDist, Function.comp_def] using h

/-- L4 (gradient direction): on the sphere, for a tangent velocity the inner product with `ω` equals
the inner product with the tangential projection `P_x^⊥ ω`. Hence the geodesic-distance derivative
is `⟪x', -(1/√(1-⟪x,ω⟫²)) • P_x^⊥ ω⟫`, exhibiting `-P_x^⊥ ω / √(1-⟪x,ω⟫²)` as the Riemannian
gradient. -/
theorem inner_eq_inner_tangentialProjector {x ω x' : Eucl d}
    (htangent : (⟪x', x⟫ : ℝ) = 0) :
    (⟪x', ω⟫ : ℝ) = ⟪x', tangentialProjector x ω⟫ := by
  rw [tangentialProjector_apply, inner_sub_right, real_inner_smul_right, htangent]
  ring

end MeasureToMeasure.Leaves
