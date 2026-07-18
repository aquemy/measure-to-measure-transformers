import MeasureToMeasure.Foundations.Sphere
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

/-!
# Avoiding colinearity of the mass-gap-cap-collapse targets (`lemma_3_4_part2` Gap 2, cases A & B)

`lemma_3_4_part2`'s discharge via the mass-gap-cap-collapse route (`Leaves/Lemma34Part1MeanField.lean`)
reduces to ONE remaining gap ("Gap 2", `mean-field-axioms-retractability` project notes): the
construction proves the flowed barycenters are UNEQUAL, but the axiom needs them NON-COLINEAR for
every `γ₂`. The collapse-target vectors are `Sμ•ω(θ)+p` and `Sν•ω(θ)+q` (`Sμ,Sν` cap masses, `p,q`
leftover-mass integrals, `ω(θ) := cosθ•z+sinθ•w` the cap-pole curve parametrized by the auxiliary
direction `w`), and the question is which `θ` make these colinear.

**Case A** (easiest): writing `p,q`'s components orthogonal to `span{z,w}` as `restComp z w p`,
`restComp z w q` (θ-INDEPENDENT, since `ω(θ)` lies entirely in `span{z,w}` --
`restComp_add_smul_omega`), if these rest-components are NOT scalar multiples of each other, the
collapse targets can NEVER be colinear, for ANY `θ` or `γ₂` (`ne_smul_collapse_of_restComp_not_smul`)
-- the rest-component mismatch alone rules it out, since a colinear pair would need proportional
rest-components too.

**Combined with `Leaves/PoleGeometry.lean`'s `exists_unit_orthogonal_two`** (`d≥3`, choose `w⊥{z,q}`
so `q`'s rest-component is exactly `q`'s component orthogonal to `z` alone, independent of `w`), this
handles the case `q ∦ z` (or symmetrically `p ∦ z`) entirely, WHENEVER `p`'s own rest-component (now
pinned to `p - ⟨p,z⟩z - ⟨p,w⟩w` for the specific chosen `w`) also fails to be parallel to `q`'s.

**Case B**: when the rest-components ARE parallel (`restComp z w p = r₀ • restComp z w q` for a forced
ratio `r₀`, with `restComp z w q ≠ 0`), any colinearity witness `γ` at any angle `θ` is FORCED to equal
`r₀` (`gamma_eq_r0_of_colinear` -- same rest-component argument as Case A, but pinning `γ` instead of
refuting it). Substituting `γ = r₀` back into the colinearity equation and taking `z`- and
`w`-components (`ω(θ)` lies in `span{z,w}`, so this captures the whole equation together with the
already-matched rest-components) yields a LINEAR system `(Sμ-r₀Sν)cosθ = r₀q_z-p_z`,
`(Sμ-r₀Sν)sinθ = r₀q_w-p_w` (`cos_eq_of_colinear`, `sin_eq_of_colinear`). Whenever `Sμ ≠ r₀Sν`, this
system pins `cosθ,sinθ` uniquely, so **at most one angle (mod 2π) can be colinear**
(`angle_unique_of_colinear`, via `Real.Angle.cos_sin_inj`) -- combined with the existing 2-candidate
cap-pole pigeonhole (`exists_pole_in_cap_ne`), the OTHER candidate angle is then guaranteed safe.

**NOT yet done** (see `mean-field-axioms-retractability` for the full derivation): the residual case
(`Sμ = r₀Sν` as well, a narrow 4-way conjunctive degeneracy) is not excluded here, nor is `restComp z w
q = 0`. The final assembly connecting these standalone lemmas to `Lemma34Part1MeanField.lean`'s actual
`μ, ν, z, w, p, q, Sμ, Sν` instantiation, and wiring the 2-candidate pigeonhole through
`angle_unique_of_colinear`, is NOT attempted here.
-/

namespace MeasureToMeasure.Leaves

open scoped RealInnerProductSpace

variable {d : ℕ}

/-- The component of `v` orthogonal to both `z` and `w`. -/
noncomputable def restComp (z w v : Eucl d) : Eucl d := v - (⟪z, v⟫ : ℝ) • z - (⟪w, v⟫ : ℝ) • w

/-- `restComp` is linear in its third argument. -/
theorem restComp_smul {z w v : Eucl d} (c : ℝ) : restComp z w (c • v) = c • restComp z w v := by
  unfold restComp
  simp only [real_inner_smul_right, smul_sub, smul_smul]

/-- If `A`'s rest-component (relative to `z,w`) is NOT a scalar multiple of `B`'s, `A` is never a
scalar multiple of `B` -- the rest-components alone rule out colinearity. -/
theorem ne_smul_of_restComp_not_smul {z w A B : Eucl d}
    (hne : ∀ c : ℝ, restComp z w A ≠ c • restComp z w B) (γ₂ : ℝ) : A ≠ γ₂ • B := by
  intro h
  apply hne γ₂
  show A - (⟪z, A⟫ : ℝ) • z - (⟪w, A⟫ : ℝ) • w = γ₂ • (B - (⟪z, B⟫ : ℝ) • z - (⟪w, B⟫ : ℝ) • w)
  rw [h]
  simp only [real_inner_smul_right, smul_sub, smul_smul]

/-- Since `ω(θ) := cosθ•z + sinθ•w` lies entirely in `span{z,w}`, adding `Sμ•ω(θ)` to a vector `p`
doesn't change its rest-component relative to orthonormal `z,w`. -/
theorem restComp_add_smul_omega {z w p : Eucl d} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (hzw : (⟪z, w⟫ : ℝ) = 0) (Sμ θ : ℝ) :
    restComp z w (Sμ • (Real.cos θ • z + Real.sin θ • w) + p) = restComp z w p := by
  have hzz : (⟪z, z⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hz]; norm_num
  have hww : (⟪w, w⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  have hwz : (⟪w, z⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact hzw
  unfold restComp
  simp only [inner_add_right, real_inner_smul_right, hzz, hww, hzw, hwz]
  module

/-- **Case A: rest-components not parallel ⟹ NEVER colinear, for any pole angle `θ` or scalar
`γ₂`.** If the leftover-mass integrals `p,q`'s components orthogonal to `span{z,w}` are not scalar
multiples of each other, the collapse-target vectors `Sμ•ω(θ)+p` and `Sν•ω(θ)+q` can never be
colinear, for every `θ` and every `γ₂`. -/
theorem ne_smul_collapse_of_restComp_not_smul {z w p q : Eucl d} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (hzw : (⟪z, w⟫ : ℝ) = 0) (Sμ Sν : ℝ)
    (hne : ∀ c : ℝ, restComp z w p ≠ c • restComp z w q) (θ γ₂ : ℝ) :
    Sμ • (Real.cos θ • z + Real.sin θ • w) + p
      ≠ γ₂ • (Sν • (Real.cos θ • z + Real.sin θ • w) + q) := by
  apply ne_smul_of_restComp_not_smul
  intro c
  rw [restComp_add_smul_omega hz hw hzw, restComp_add_smul_omega hz hw hzw]
  exact hne c

/-- **Case B step 1: the colinearity ratio is forced.** If `p,q`'s rest-components are parallel with
ratio `r₀` and `q`'s rest-component is nonzero, ANY colinearity witness `γ` (at any angle `θ`) must
equal `r₀` -- the rest-component match alone pins it, since `q`'s rest-component is a nonzero vector
whose scalar multiples are distinct. -/
theorem gamma_eq_r0_of_colinear {z w p q : Eucl d} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (hzw : (⟪z, w⟫ : ℝ) = 0)
    {Sμ Sν r₀ γ θ : ℝ} (hr : restComp z w p = r₀ • restComp z w q) (hq0 : restComp z w q ≠ 0)
    (h : Sμ • (Real.cos θ • z + Real.sin θ • w) + p
           = γ • (Sν • (Real.cos θ • z + Real.sin θ • w) + q)) :
    γ = r₀ := by
  have hL : restComp z w (Sμ • (Real.cos θ • z + Real.sin θ • w) + p) = r₀ • restComp z w q := by
    rw [restComp_add_smul_omega hz hw hzw]; exact hr
  have hR : restComp z w (γ • (Sν • (Real.cos θ • z + Real.sin θ • w) + q))
      = γ • restComp z w q := by
    rw [restComp_smul, restComp_add_smul_omega hz hw hzw]
  rw [h, hR] at hL
  have heq : (r₀ - γ) • restComp z w q = 0 := by
    rw [sub_smul, hL]; abel
  rcases smul_eq_zero.mp heq with h1 | h1
  · linarith [sub_eq_zero.mp h1]
  · exact absurd h1 hq0

/-- **Case B step 2a: the `z`-component of a (ratio-`r₀`) colinearity equation is a linear equation
in `cosθ`.** -/
theorem cos_eq_of_colinear {z w p q : Eucl d} (hz : ‖z‖ = 1) (hzw : (⟪z, w⟫ : ℝ) = 0)
    {Sμ Sν r₀ θ : ℝ}
    (h : Sμ • (Real.cos θ • z + Real.sin θ • w) + p
           = r₀ • (Sν • (Real.cos θ • z + Real.sin θ • w) + q)) :
    (Sμ - r₀ * Sν) * Real.cos θ = r₀ * (⟪z, q⟫ : ℝ) - (⟪z, p⟫ : ℝ) := by
  have hzz : (⟪z, z⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hz]; norm_num
  have := congrArg (fun v => (⟪z, v⟫ : ℝ)) h
  simp only [inner_add_right, inner_smul_right, hzz, hzw] at this
  ring_nf at this ⊢
  linarith [this]

/-- **Case B step 2b: the `w`-component**, symmetric to `cos_eq_of_colinear`. -/
theorem sin_eq_of_colinear {z w p q : Eucl d} (hw : ‖w‖ = 1) (hzw : (⟪z, w⟫ : ℝ) = 0)
    {Sμ Sν r₀ θ : ℝ}
    (h : Sμ • (Real.cos θ • z + Real.sin θ • w) + p
           = r₀ • (Sν • (Real.cos θ • z + Real.sin θ • w) + q)) :
    (Sμ - r₀ * Sν) * Real.sin θ = r₀ * (⟪w, q⟫ : ℝ) - (⟪w, p⟫ : ℝ) := by
  have hww : (⟪w, w⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  have hwz : (⟪w, z⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact hzw
  have := congrArg (fun v => (⟪w, v⟫ : ℝ)) h
  simp only [inner_add_right, inner_smul_right, hww, hwz] at this
  ring_nf at this ⊢
  linarith [this]

/-- **Case B step 3: a linear system with a nonzero coefficient pins the angle uniquely** (mod `2π`),
via `Real.Angle.cos_sin_inj`. -/
theorem angle_eq_of_linear_system (k RHS1 RHS2 θ₁ θ₂ : ℝ) (hk : k ≠ 0)
    (h1a : k * Real.cos θ₁ = RHS1) (h1b : k * Real.sin θ₁ = RHS2)
    (h2a : k * Real.cos θ₂ = RHS1) (h2b : k * Real.sin θ₂ = RHS2) :
    (θ₁ : Real.Angle) = (θ₂ : Real.Angle) := by
  have hc : Real.cos θ₁ = Real.cos θ₂ := mul_left_cancel₀ hk (h1a.trans h2a.symm)
  have hs : Real.sin θ₁ = Real.sin θ₂ := mul_left_cancel₀ hk (h1b.trans h2b.symm)
  exact Real.Angle.cos_sin_inj hc hs

/-- **Case B assembly: at most one angle can be colinear**, given parallel-but-nonzero rest-components
(forced ratio `r₀`) and `Sμ ≠ r₀Sν`. Any two colinearity witnesses at angles `θ₁, θ₂` (with any scalars
`γ₁, γ₂`) force `θ₁ = θ₂` as angles mod `2π` -- combined with a 2-candidate cap-pole pigeonhole giving
two DISTINCT angles, this rules out one of them being colinear. -/
theorem angle_unique_of_colinear {z w p q : Eucl d} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (hzw : (⟪z, w⟫ : ℝ) = 0) {Sμ Sν r₀ : ℝ} (hr : restComp z w p = r₀ • restComp z w q)
    (hq0 : restComp z w q ≠ 0) (hSne : Sμ ≠ r₀ * Sν)
    {θ₁ θ₂ γ₁ γ₂ : ℝ}
    (h1 : Sμ • (Real.cos θ₁ • z + Real.sin θ₁ • w) + p
            = γ₁ • (Sν • (Real.cos θ₁ • z + Real.sin θ₁ • w) + q))
    (h2 : Sμ • (Real.cos θ₂ • z + Real.sin θ₂ • w) + p
            = γ₂ • (Sν • (Real.cos θ₂ • z + Real.sin θ₂ • w) + q)) :
    (θ₁ : Real.Angle) = (θ₂ : Real.Angle) := by
  have hg1 : γ₁ = r₀ := gamma_eq_r0_of_colinear hz hw hzw hr hq0 h1
  have hg2 : γ₂ = r₀ := gamma_eq_r0_of_colinear hz hw hzw hr hq0 h2
  rw [hg1] at h1
  rw [hg2] at h2
  exact angle_eq_of_linear_system (Sμ - r₀ * Sν) (r₀ * (⟪z, q⟫ : ℝ) - (⟪z, p⟫ : ℝ))
    (r₀ * (⟪w, q⟫ : ℝ) - (⟪w, p⟫ : ℝ)) θ₁ θ₂ (sub_ne_zero.mpr hSne)
    (cos_eq_of_colinear hz hzw h1) (sin_eq_of_colinear hw hzw h1)
    (cos_eq_of_colinear hz hzw h2) (sin_eq_of_colinear hw hzw h2)

end MeasureToMeasure.Leaves
