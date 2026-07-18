import MeasureToMeasure.Foundations.Sphere

/-!
# Avoiding colinearity of the mass-gap-cap-collapse targets (`lemma_3_4_part2` Gap 2, case A)

`lemma_3_4_part2`'s discharge via the mass-gap-cap-collapse route (`Leaves/Lemma34Part1MeanField.lean`)
reduces to ONE remaining gap ("Gap 2", `mean-field-axioms-retractability` project notes): the
construction proves the flowed barycenters are UNEQUAL, but the axiom needs them NON-COLINEAR for
every `γ₂`. The collapse-target vectors are `Sμ•ω(θ)+p` and `Sν•ω(θ)+q` (`Sμ,Sν` cap masses, `p,q`
leftover-mass integrals, `ω(θ) := cosθ•z+sinθ•w` the cap-pole curve parametrized by the auxiliary
direction `w`), and the question is which `θ` make these colinear.

**This file proves the EASIEST of several cases identified by hand-analysis**: writing `p,q`'s
components orthogonal to `span{z,w}` as `restComp z w p`, `restComp z w q` (θ-INDEPENDENT, since
`ω(θ)` lies entirely in `span{z,w}` -- `restComp_add_smul_omega`), if these rest-components are NOT
scalar multiples of each other, the collapse targets can NEVER be colinear, for ANY `θ` or `γ₂`
(`ne_smul_collapse_of_restComp_not_smul`) -- the rest-component mismatch alone rules it out, since a
colinear pair would need proportional rest-components too.

**Combined with `Leaves/PoleGeometry.lean`'s `exists_unit_orthogonal_two`** (`d≥3`, choose `w⊥{z,q}`
so `q`'s rest-component is exactly `q`'s component orthogonal to `z` alone, independent of `w`), this
handles the case `q ∦ z` (or symmetrically `p ∦ z`) entirely, WHENEVER `p`'s own rest-component (now
pinned to `p - ⟨p,z⟩z - ⟨p,w⟩w` for the specific chosen `w`) also fails to be parallel to `q`'s.

**NOT yet done** (see `mean-field-axioms-retractability` for the full derivation): the remaining case
(`p`'s and `q`'s rest-components ARE parallel, with a FORCED ratio `r₀`) reduces to a LINEAR system in
`cosθ, sinθ` -- at most one solution `θ` (via `Real.Angle.cos_sin_inj`, confirmed available) unless a
narrow 4-way conjunctive degeneracy holds. That case, and the final assembly into `lemma_3_4_part2`
itself, are NOT attempted here.
-/

namespace MeasureToMeasure.Leaves

open scoped RealInnerProductSpace

variable {d : ℕ}

/-- The component of `v` orthogonal to both `z` and `w`. -/
noncomputable def restComp (z w v : Eucl d) : Eucl d := v - (⟪z, v⟫ : ℝ) • z - (⟪w, v⟫ : ℝ) • w

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

end MeasureToMeasure.Leaves
