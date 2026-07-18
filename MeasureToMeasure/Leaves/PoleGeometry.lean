import MeasureToMeasure.Foundations.Sphere
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Leaf (Lemma 3.4 Part 1, Path I assembly): two spherical-cap geometry facts

Two purely geometric ingredients the grand assembly needs:

* `exists_unit_orthogonal` — for `2 ≤ d`, every direction `z` admits a **unit vector orthogonal to
  it**. This is what feeds `exists_pole_in_cap_ne` (the cap-pole pigeonhole needs a unit `w ⊥ z`), and
  it is the sole place the recovered dimension bound `2 ≤ d` is consumed.

* `inner_pole_lower_bound` — the **tangential Cauchy–Schwarz** bound: for unit `z, x, ω`,
  `⟪x, ω⟫ ≥ ⟪z,x⟫·⟪z,ω⟫ − √(1−⟪z,x⟫²)·√(1−⟪z,ω⟫²)`. Splitting `x, ω` into their `z`-components and
  orthogonal residuals, `⟪x,ω⟫ = ⟪z,x⟫⟪z,ω⟫ + ⟪x⊥, ω⊥⟫`, and Cauchy–Schwarz bounds the residual pairing
  below by `−‖x⊥‖‖ω⊥‖ = −√(1−⟪z,x⟫²)√(1−⟪z,ω⟫²)`. This gives the uniform pole-reach floor `mp` on a
  sub-cap `{⟪z,·⟫ ≥ m}` for an off-centre pole `ω` (specialising to `mp = m` when `ω = z`).
-/

namespace MeasureToMeasure.Leaves

open scoped RealInnerProductSpace

variable {d : ℕ}

/-- **A unit vector orthogonal to any direction, when `2 ≤ d`.** The orthogonal complement of the line
`ℝ ∙ z` has dimension `≥ d − 1 ≥ 1`, hence a nonzero vector; normalise it. -/
theorem exists_unit_orthogonal (hd : 2 ≤ d) {z : Eucl d} (hz0 : z ≠ 0) :
    ∃ w : Eucl d, (⟪z, w⟫ : ℝ) = 0 ∧ ‖w‖ = 1 := by
  have hspan : Module.finrank ℝ ↥(ℝ ∙ z) = 1 := finrank_span_singleton hz0
  have hsum := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (E := Eucl d) (ℝ ∙ z)
  have hdim : Module.finrank ℝ (Eucl d) = d := by rw [finrank_euclideanSpace, Fintype.card_fin]
  have hpos : 0 < Module.finrank ℝ ↥(ℝ ∙ z)ᗮ := by omega
  have hnt : Nontrivial ↥(ℝ ∙ z)ᗮ := Module.finrank_pos_iff.mp hpos
  obtain ⟨u, hune⟩ := exists_ne (0 : ↥(ℝ ∙ z)ᗮ)
  have hvne : (u : Eucl d) ≠ 0 := fun h => hune (Submodule.coe_eq_zero.mp h)
  have hvz : (⟪z, (u : Eucl d)⟫ : ℝ) = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp u.2
  refine ⟨‖(u : Eucl d)‖⁻¹ • (u : Eucl d), ?_, ?_⟩
  · rw [real_inner_smul_right, hvz, mul_zero]
  · rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hvne)]

/-- **A unit vector orthogonal to TWO given vectors, when `3 ≤ d`.** Generalizes
`exists_unit_orthogonal` (which only avoids `z`) via the same orthogonal-complement dimension-count,
applied to `span{z,v}` (dimension `≤ 2`) instead of `span{z}` (dimension `1`): the complement then has
dimension `≥ d-2 ≥ 1`. Staged for `lemma_3_4_part2`'s Gap 2 (`mean-field-axioms-retractability` project
notes): choosing the cap-pole construction's auxiliary direction `w` orthogonal to BOTH the cap
direction `z` and a leftover-mass integral `v` makes `v`'s component orthogonal to `span(z,w)` equal
`v`'s component orthogonal to `z` alone (independent of `w`), sidestepping the worst degenerate
sub-case of the non-colinearity argument whenever that component is nonzero. -/
theorem exists_unit_orthogonal_two (hd : 3 ≤ d) {z : Eucl d} (hz0 : z ≠ 0) (v : Eucl d) :
    ∃ w : Eucl d, (⟪z, w⟫ : ℝ) = 0 ∧ (⟪v, w⟫ : ℝ) = 0 ∧ ‖w‖ = 1 := by
  classical
  set S : Submodule ℝ (Eucl d) := Submodule.span ℝ {z, v} with hSdef
  have hSdim : Module.finrank ℝ ↥S ≤ 2 := by
    rw [hSdef]
    calc Module.finrank ℝ ↥(Submodule.span ℝ ({z, v} : Set (Eucl d)))
        ≤ ({z, v} : Set (Eucl d)).toFinset.card := finrank_span_le_card _
      _ ≤ 2 := by
          rw [Set.toFinset_insert, Set.toFinset_singleton]
          exact (Finset.card_insert_le _ _).trans (by simp)
  have hsum := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (E := Eucl d) S
  have hdim : Module.finrank ℝ (Eucl d) = d := by rw [finrank_euclideanSpace, Fintype.card_fin]
  have hpos : 0 < Module.finrank ℝ ↥Sᗮ := by omega
  have hnt : Nontrivial ↥Sᗮ := Module.finrank_pos_iff.mp hpos
  obtain ⟨u, hune⟩ := exists_ne (0 : ↥Sᗮ)
  have hvne : (u : Eucl d) ≠ 0 := fun h => hune (Submodule.coe_eq_zero.mp h)
  have hzS : z ∈ S := Submodule.subset_span (by simp)
  have hvS : v ∈ S := Submodule.subset_span (by simp)
  have hortho := (Submodule.mem_orthogonal S (u : Eucl d)).mp u.2
  have hzu : (⟪z, (u : Eucl d)⟫ : ℝ) = 0 := hortho z hzS
  have hvu : (⟪v, (u : Eucl d)⟫ : ℝ) = 0 := hortho v hvS
  refine ⟨‖(u : Eucl d)‖⁻¹ • (u : Eucl d), ?_, ?_, ?_⟩
  · rw [real_inner_smul_right, hzu, mul_zero]
  · rw [real_inner_smul_right, hvu, mul_zero]
  · rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hvne)]

/-- **Tangential Cauchy–Schwarz lower bound.** For unit `z, x, ω`,
`⟪z,x⟫·⟪z,ω⟫ − √(1−⟪z,x⟫²)·√(1−⟪z,ω⟫²) ≤ ⟪x, ω⟫`. Proof: `⟪x,ω⟫ = ⟪z,x⟫⟪z,ω⟫ + ⟪x⊥, ω⊥⟫` with
`x⊥ = x − ⟪z,x⟫z`, `ω⊥ = ω − ⟪z,ω⟫z`, and `⟪x⊥,ω⊥⟫ ≥ −‖x⊥‖‖ω⊥‖ = −√(1−⟪z,x⟫²)√(1−⟪z,ω⟫²)`. -/
theorem inner_pole_lower_bound {z x ω : Eucl d} (hz : ‖z‖ = 1) (hx : ‖x‖ = 1) (hω : ‖ω‖ = 1) :
    (⟪z, x⟫ : ℝ) * ⟪z, ω⟫ - Real.sqrt (1 - (⟪z, x⟫ : ℝ) ^ 2) * Real.sqrt (1 - (⟪z, ω⟫ : ℝ) ^ 2)
      ≤ (⟪x, ω⟫ : ℝ) := by
  have hzz : (⟪z, z⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hz]; norm_num
  have hxx : (⟪x, x⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hx]; norm_num
  have hww : (⟪ω, ω⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hω]; norm_num
  set xp : Eucl d := x - (⟪z, x⟫ : ℝ) • z with hxp
  set wp : Eucl d := ω - (⟪z, ω⟫ : ℝ) • z with hwp
  -- residual pairing: ⟪xp, wp⟫ = ⟪x,ω⟫ − ⟪z,x⟫·⟪z,ω⟫
  have hres : (⟪xp, wp⟫ : ℝ) = ⟪x, ω⟫ - ⟪z, x⟫ * ⟪z, ω⟫ := by
    simp only [hxp, hwp, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hzz]
    rw [real_inner_comm x z]; ring
  -- residual norms: ‖xp‖² = 1 − ⟪z,x⟫², ‖wp‖² = 1 − ⟪z,ω⟫²
  have hxpn2 : ‖xp‖ ^ 2 = 1 - (⟪z, x⟫ : ℝ) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [hxp, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      hzz, hxx]
    rw [real_inner_comm x z]; ring
  have hwpn2 : ‖wp‖ ^ 2 = 1 - (⟪z, ω⟫ : ℝ) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [hwp, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      hzz, hww]
    rw [real_inner_comm ω z]; ring
  have hxpnorm : ‖xp‖ = Real.sqrt (1 - (⟪z, x⟫ : ℝ) ^ 2) := by
    rw [← hxpn2, Real.sqrt_sq (norm_nonneg _)]
  have hwpnorm : ‖wp‖ = Real.sqrt (1 - (⟪z, ω⟫ : ℝ) ^ 2) := by
    rw [← hwpn2, Real.sqrt_sq (norm_nonneg _)]
  -- Cauchy–Schwarz on the residuals
  have hcs : -(‖xp‖ * ‖wp‖) ≤ (⟪xp, wp⟫ : ℝ) := (abs_le.mp (abs_real_inner_le_norm xp wp)).1
  rw [hxpnorm, hwpnorm] at hcs
  linarith [hres, hcs]

end MeasureToMeasure.Leaves
