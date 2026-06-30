import MeasureToMeasure.Foundations.Projector
import MeasureToMeasure.Foundations.GeodesicDistance

/-!
# Leaf L2: the gate algebra and the gate ODE (eq. B.4-B.5)

In Lemma B.2 the parameters `U = -𝟙 zᵀ`, `b = cos(R) 𝟙`, `W 𝟙 = ω` give the ReLU-gated velocity
`W(Ux+b)₊ = (cos R - ⟪z, x⟫)₊ ω`. Projected onto the tangent space, the characteristic satisfies

    d/dt ⟪x(t), ω⟫ = (gate)·(1 - ⟪x(t), ω⟫²),     gate = (cos R - ⟪z, x⟫)₊,

which is positive exactly on the active region `{x : ⟪z, x⟫ < cos R} = {x : d_g(z, x) > R}` (eq. B.4).
This drives `⟪x, ω⟫` upward, i.e. pushes `x` toward `ω`.

We kernel-check three facts:
* `gate_inner_identity` (the algebra behind B.5): `⟪P_x^⊥ (g•ω), ω⟫ = g(1 - ⟪x,ω⟫²)`;
* `gate_hasDerivAt_inner` (B.5 itself): the derivative of `⟪x(t), ω⟫` along the gated flow;
* `gate_pos_iff` / `gate_pos_iff_dist` (B.4): the active region described two ways.
-/

namespace MeasureToMeasure.Leaves

open scoped RealInnerProductSpace
open MeasureToMeasure

variable {d : ℕ}

/-- L2 (algebra of B.5): for unit `x` and unit `ω`, projecting the scaled drift `g•ω` and pairing
with `ω` gives the logistic factor `g(1 - ⟪x,ω⟫²)`. -/
theorem gate_inner_identity {x ω : Eucl d} (hx : x ∈ sphere d) (hω : ω ∈ sphere d) (g : ℝ) :
    ⟪tangentialProjector x (g • ω), ω⟫ = g * (1 - ⟪x, ω⟫ ^ 2) := by
  rw [tangentialProjector_smul, real_inner_smul_left, projector_inner_sub_sq hx ω,
    norm_eq_one_of_mem_sphere hω, one_pow]

/-- L2 (the gate ODE B.5): along a path `x(t)` on the sphere whose velocity is the projected gated
drift `x'(t) = P_{x(t)}^⊥ (g • ω)`, the inner product `⟪x(t), ω⟫` evolves as
`g(1 - ⟪x(t), ω⟫²)`. -/
theorem gate_hasDerivAt_inner {x : ℝ → Eucl d} {ω : Eucl d} {t : ℝ} {x' : Eucl d}
    (hx : HasDerivAt x x' t) (hxs : x t ∈ sphere d) (hω : ω ∈ sphere d) (g : ℝ)
    (hode : x' = tangentialProjector (x t) (g • ω)) :
    HasDerivAt (fun s => (⟪x s, ω⟫ : ℝ)) (g * (1 - ⟪x t, ω⟫ ^ 2)) t := by
  have hconst : HasDerivAt (fun _ : ℝ => ω) (0 : Eucl d) t := hasDerivAt_const t ω
  have h := hx.inner ℝ hconst
  rw [hode, gate_inner_identity hxs hω g] at h
  simpa using h

/-- L2 (gate sign, B.4, affine form): the pre-ReLU gate `cos R - ⟪z, x⟫` is positive exactly when
`⟪z, x⟫ < cos R`. -/
theorem gate_pos_iff (z x : Eucl d) (R : ℝ) :
    0 < Real.cos R - (⟪z, x⟫ : ℝ) ↔ (⟪z, x⟫ : ℝ) < Real.cos R := by
  constructor <;> intro h <;> linarith

/-- L2 (gate sign, B.4, geodesic form): the gate is active exactly outside the closed cap of radius
`R` around `z`, i.e. on `{x : d_g(z, x) > R}`. -/
theorem gate_pos_iff_dist {z x : Eucl d} (hz : z ∈ sphere d) (hx : x ∈ sphere d)
    {R : ℝ} (hR : R ∈ Set.Icc (0 : ℝ) Real.pi) :
    (⟪z, x⟫ : ℝ) < Real.cos R ↔ R < geodesicDist z x := by
  rw [← cos_geodesicDist hz hx]
  exact Real.strictAntiOn_cos.lt_iff_gt (geodesicDist_mem_Icc z x) hR

end MeasureToMeasure.Leaves
