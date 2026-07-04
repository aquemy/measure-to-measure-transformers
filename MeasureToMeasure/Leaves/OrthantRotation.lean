import MeasureToMeasure.Leaves.GatedTwoCap
import MeasureToMeasure.Foundations.GeodesicConvex

/-!
# The two-phase rotation into the positive orthant (Lemma 3.2, dynamical core)

The paper's Lemma 3.2 (p.15) moves a family of sphere measures with a shared missing direction
`ω` into the open orthant with two constant perceptron phases: push away from `ω`, then pull
toward an interior orthant direction. This file machine-checks the pointwise transport:

* `exists_unit_orthant_ne`: for `d ≥ 2` the positive part of the sphere has a unit direction
  `α ≠ ω` with a uniform coordinate floor `c` (two explicit candidates, one of which must
  differ from `ω`).
* `cap_pos_coords`: a sphere point in the inner cap of level `1 - c²/8` around such an `α` has
  all coordinates positive (polarization plus the coordinate-projection bound).
* `exists_twoPhase_mapsTo_orthant`: the two-block schedule realizing the rotation. Phase 1 is
  the self-centered scaled gated block toward `-ω` with sub-threshold gate level `cosR = -1`
  (active everywhere except the antipode `ω`, which the missing-direction gap keeps mass away
  from); phase 2 the same machinery toward `α`. Amplitudes come from
  `exists_scaledGatedBlock_mapsTo_cap`, so any horizon `T > 0` works.

The dimension hypothesis `2 ≤ d` is load-bearing: on the `0`-sphere every radially tangent
field vanishes at both points, so no flow can move `δ_{-e₀}` into the orthant `{+e₀}`
(finding F18; the kernel-checked disproof of the `d = 1` instance is
`Regression.Refuted.oldLemma32Family_dimOne_false`).
-/

namespace MeasureToMeasure.Leaves

open MeasureToMeasure
open scoped RealInnerProductSpace

variable {d : ℕ}

/-- For `d ≥ 2` there is a unit vector with a uniform positive coordinate floor that differs
from any prescribed `ω`: of the two explicit candidates `𝟙/‖𝟙‖` and `(𝟙 + e₀)/‖𝟙 + e₀‖`
(coordinate patterns constant resp. non-constant), at most one can equal `ω`. -/
theorem exists_unit_orthant_ne (hd : 2 ≤ d) (ω : Eucl d) :
    ∃ (α : Eucl d) (c : ℝ), ‖α‖ = 1 ∧ 0 < c ∧ (∀ i, c ≤ α i) ∧ α ≠ ω := by
  have hd0 : 0 < d := lt_of_lt_of_le two_pos hd
  have hd1 : 1 < d := lt_of_lt_of_le one_lt_two hd
  set i0 : Fin d := ⟨0, hd0⟩ with hi0
  set i1 : Fin d := ⟨1, hd1⟩ with hi1
  have hne01 : i0 ≠ i1 := by simp [hi0, hi1, Fin.ext_iff]
  -- the two raw candidates
  set v₁ : Eucl d := WithLp.toLp 2 (fun _ => (1 : ℝ)) with hv₁
  set v₂ : Eucl d := v₁ + EuclideanSpace.single i0 (1 : ℝ) with hv₂
  have hv₁c : ∀ i, v₁ i = 1 := fun i => rfl
  have hv₂0 : v₂ i0 = 2 := by
    simp [hv₂, hv₁, PiLp.add_apply]; norm_num
  have hv₂1 : v₂ i1 = 1 := by
    simp [hv₂, hv₁, hne01.symm]
  have hv₂pos : ∀ i, (1 : ℝ) ≤ v₂ i := by
    intro i
    by_cases h : i = i0
    · subst h; rw [hv₂0]; norm_num
    · simp [hv₂, hv₁, Ne.symm h]
  -- norms are positive
  have hv₁norm : 0 < ‖v₁‖ := by
    have : v₁ i0 ≠ 0 := by rw [hv₁c]; norm_num
    have hne : v₁ ≠ 0 := fun h => this (by rw [h]; rfl)
    exact norm_pos_iff.mpr hne
  have hv₂norm : 0 < ‖v₂‖ := by
    have : v₂ i0 ≠ 0 := by rw [hv₂0]; norm_num
    have hne : v₂ ≠ 0 := fun h => this (by rw [h]; rfl)
    exact norm_pos_iff.mpr hne
  -- the normalized candidates, their floors, and distinctness
  set u₁ : Eucl d := ‖v₁‖⁻¹ • v₁ with hu₁
  set u₂ : Eucl d := ‖v₂‖⁻¹ • v₂ with hu₂
  have hu₁norm : ‖u₁‖ = 1 := norm_smul_inv_norm (norm_pos_iff.mp hv₁norm)
  have hu₂norm : ‖u₂‖ = 1 := norm_smul_inv_norm (norm_pos_iff.mp hv₂norm)
  have hu₁coord : ∀ i, ‖v₁‖⁻¹ ≤ u₁ i := by
    intro i
    have : u₁ i = ‖v₁‖⁻¹ * v₁ i := rfl
    rw [this, hv₁c, mul_one]
  have hu₂coord : ∀ i, ‖v₂‖⁻¹ ≤ u₂ i := by
    intro i
    have hcoord : u₂ i = ‖v₂‖⁻¹ * v₂ i := rfl
    have hinv : 0 < ‖v₂‖⁻¹ := inv_pos.mpr hv₂norm
    calc ‖v₂‖⁻¹ = ‖v₂‖⁻¹ * 1 := (mul_one _).symm
      _ ≤ ‖v₂‖⁻¹ * v₂ i := by
          exact mul_le_mul_of_nonneg_left (hv₂pos i) hinv.le
      _ = u₂ i := hcoord.symm
  have hu₁u₂ : u₁ ≠ u₂ := by
    intro h
    -- u₁ has equal coordinates at i0, i1; u₂ does not
    have h0 : u₁ i0 = u₂ i0 := by rw [h]
    have h1 : u₁ i1 = u₂ i1 := by rw [h]
    have hu₁eq : u₁ i0 = u₁ i1 := by
      show ‖v₁‖⁻¹ * v₁ i0 = ‖v₁‖⁻¹ * v₁ i1
      rfl
    have hu₂ne : u₂ i0 ≠ u₂ i1 := by
      show ‖v₂‖⁻¹ * v₂ i0 ≠ ‖v₂‖⁻¹ * v₂ i1
      rw [hv₂0, hv₂1]
      have hinv : ‖v₂‖⁻¹ ≠ 0 := (inv_pos.mpr hv₂norm).ne'
      intro hcon
      have := mul_left_cancel₀ hinv hcon
      norm_num at this
    exact hu₂ne (by rw [← h0, ← h1, hu₁eq])
  -- pick the candidate that differs from ω
  by_cases hcase : u₁ = ω
  · exact ⟨u₂, ‖v₂‖⁻¹, hu₂norm, inv_pos.mpr hv₂norm, hu₂coord,
      fun h => hu₁u₂ (hcase.trans h.symm)⟩
  · exact ⟨u₁, ‖v₁‖⁻¹, hu₁norm, inv_pos.mpr hv₁norm, hu₁coord, hcase⟩

/-- **Cap into the orthant.** A sphere point in the inner cap of level `1 - c²/8` around a unit
vector with coordinate floor `c > 0` has all coordinates positive: the cap has Euclidean radius
`c/2` (polarization), and each coordinate moves by at most the Euclidean distance. -/
theorem cap_pos_coords {α y : Eucl d} {c : ℝ} (hα : ‖α‖ = 1) (hc : 0 < c)
    (hcoord : ∀ i, c ≤ α i) (hy : y ∈ sphere d) (hcap : 1 - c ^ 2 / 8 ≤ ⟪α, y⟫) :
    ∀ i, 0 < y i := by
  intro i
  have hr : (0 : ℝ) < c / 2 := by linarith
  have hcap' : 1 - (c / 2) ^ 2 / 2 ≤ ⟪α, y⟫ := by
    have : (c / 2) ^ 2 / 2 = c ^ 2 / 8 := by ring
    rw [this]; exact hcap
  have hdist : dist y α ≤ c / 2 :=
    dist_le_of_inner_cap hα hy hr hcap'
  -- coordinate projection bound: |y i - α i| ≤ ‖y - α‖
  have hproj : |y i - α i| ≤ ‖y - α‖ := by
    have hsingle : ⟪EuclideanSpace.single i (1 : ℝ), y - α⟫ = (y - α) i := by
      simp [EuclideanSpace.inner_single_left]
    have hnorm1 : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by
      simp
    have hcs := abs_real_inner_le_norm (EuclideanSpace.single i (1 : ℝ)) (y - α)
    rw [hsingle, hnorm1, one_mul] at hcs
    simpa using hcs
  have hsub : (y - α) i = y i - α i := rfl
  rw [← dist_eq_norm] at hproj
  have hlow : α i - c / 2 ≤ y i := by
    have h1 : |y i - α i| ≤ c / 2 := le_trans (by rw [← hsub]; exact hproj) hdist
    have h2 := abs_le.mp h1
    linarith [h2.1]
  have := hcoord i
  linarith

/-- **The two-phase rotation (Lemma 3.2, pointwise form).** For `d ≥ 2`, a unit missing
direction `ω`, a gap `δ ∈ (0, 1]`, and any horizon `T > 0`, there is a two-block schedule whose
flow map carries every sphere point with `⟪ω, x⟫ ≤ 1 - δ` to a point with all coordinates
positive. Phase 1 (push toward `-ω`) starts at gate level `≥ δ - 1 > -1` thanks to the gap;
phase 2 (pull toward the orthant direction `α ≠ ω`) starts clear of `-α` because the phase-1
target cap around `-ω` keeps a positive inner-product margin `η = 1 - ⟪α, ω⟫ > 0`. -/
theorem exists_twoPhase_mapsTo_orthant (hd : 2 ≤ d) {ω : Eucl d} (hω : ‖ω‖ = 1)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {T : ℝ} (hT : 0 < T) :
    ∃ θ : Params d, switches θ = 2 ∧
      Set.MapsTo (flowMap θ T) {x | x ∈ sphere d ∧ (⟪ω, x⟫ : ℝ) ≤ 1 - δ}
        {y | ∀ i, 0 < y i} := by
  obtain ⟨α, c, hα, hc, hcoord, hαω⟩ := exists_unit_orthant_ne hd ω
  have hωs : ω ∈ sphere d := by
    rw [sphere, Metric.mem_sphere, dist_zero_right]; exact hω
  have hαs : α ∈ sphere d := by
    rw [sphere, Metric.mem_sphere, dist_zero_right]; exact hα
  -- the phase-2 margin η = 1 - ⟪α, ω⟫ > 0 from α ≠ ω
  set η : ℝ := 1 - ⟪α, ω⟫ with hη_def
  have hinner_le : (⟪α, ω⟫ : ℝ) ≤ 1 := by
    have := abs_real_inner_le_norm α ω
    rw [hα, hω, one_mul] at this
    exact (abs_le.mp this).2
  have hinner_ge : (-1 : ℝ) ≤ ⟪α, ω⟫ := by
    have := abs_real_inner_le_norm α ω
    rw [hα, hω, one_mul] at this
    exact (abs_le.mp this).1
  have hη0 : 0 < η := by
    rcases eq_or_ne α (-ω) with hneg | hneg
    · have : (⟪α, ω⟫ : ℝ) = -1 := by
        rw [hneg, inner_neg_left, inner_self_eq_one_of_mem_sphere hωs]
      rw [hη_def, this]; norm_num
    · have := inner_mem_Ioo_of_ne hαs hωs hαω hneg
      rw [hη_def]; linarith [this.2]
  have hη2 : η ≤ 2 := by rw [hη_def]; linarith
  -- coordinate floor of a unit vector is at most 1
  have hc1 : c ≤ 1 := by
    have hi0 : (0 : ℕ) < d := lt_of_lt_of_le two_pos hd
    have hcs := abs_real_inner_le_norm (EuclideanSpace.single (⟨0, hi0⟩ : Fin d) (1 : ℝ)) α
    have hsingle : ⟪EuclideanSpace.single (⟨0, hi0⟩ : Fin d) (1 : ℝ), α⟫ = α ⟨0, hi0⟩ := by
      simp [EuclideanSpace.inner_single_left]
    have hnorm1 : ‖EuclideanSpace.single (⟨0, hi0⟩ : Fin d) (1 : ℝ)‖ = 1 := by
      simp
    rw [hsingle, hnorm1, one_mul, hα] at hcs
    have := (abs_le.mp hcs).2
    linarith [hcoord ⟨0, hi0⟩]
  -- phase-1 data: push toward -ω from level m₁ = δ - 1 up to level b₁ = 1 - η²/8
  have hnegω : ‖-ω‖ = 1 := by rw [norm_neg]; exact hω
  have hm₁R : (-1 : ℝ) < δ - 1 := by linarith
  have hm₁1 : δ - 1 < 1 := by linarith
  have hb₁ : (1 - η ^ 2 / 8 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · nlinarith
    · nlinarith
  obtain ⟨A₁, hA₁, hMaps₁⟩ :=
    exists_scaledGatedBlock_mapsTo_cap hnegω (le_refl (-1 : ℝ)) hT hm₁R hm₁1 hb₁
  -- phase-2 data: pull toward α from level m₂ = η/2 - 1 up to level b₂ = 1 - c²/8
  have hm₂R : (-1 : ℝ) < η / 2 - 1 := by linarith
  have hm₂1 : η / 2 - 1 < 1 := by linarith
  have hb₂ : (1 - c ^ 2 / 8 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · nlinarith
    · nlinarith
  obtain ⟨A₂, hA₂, hMaps₂⟩ :=
    exists_scaledGatedBlock_mapsTo_cap hα (le_refl (-1 : ℝ)) hT hm₂R hm₂1 hb₂
  set B₁ := scaledGatedBlock hA₁ hnegω hnegω (le_refl (-1 : ℝ)) hT.le with hB₁
  set B₂ := scaledGatedBlock hA₂ hα hα (le_refl (-1 : ℝ)) hT.le with hB₂
  refine ⟨[B₁, B₂], rfl, ?_⟩
  intro x hx
  obtain ⟨hxs, hxgap⟩ := hx
  -- unfold the two-block flow
  have hflow : flowMap [B₁, B₂] T x = B₂.blockFlow T (B₁.blockFlow T x) := by
    rw [flowMap_cons, flowMap_cons, flowMap_nil]
    rfl
  -- phase 1: x is in the m₁-cap around -ω
  have hx₁ : x ∈ {z | z ∈ sphere d ∧ (δ - 1 : ℝ) ≤ ⟪z, -ω⟫} := by
    refine ⟨hxs, ?_⟩
    rw [inner_neg_right]
    rw [real_inner_comm]
    linarith
  have hy₁ := hMaps₁ hx₁
  set y := B₁.blockFlow T x with hy_def
  have hys : y ∈ sphere d := B₁.blockFlow_mem_sphere hxs hT.le
  -- bridge: y is η/2-close to -ω, hence has inner product ≥ η/2 - 1 with α
  have hy_cap : (1 - (η / 2) ^ 2 / 2 : ℝ) ≤ ⟪-ω, y⟫ := by
    have h8 : ((η / 2) ^ 2 / 2 : ℝ) = η ^ 2 / 8 := by ring
    rw [h8]
    rw [real_inner_comm]
    exact hy₁
  have hnegωs : -ω ∈ sphere d := by
    rw [sphere, Metric.mem_sphere, dist_zero_right]; exact hnegω
  have hηhalf : (0 : ℝ) < η / 2 := by linarith
  have hy_dist : dist y (-ω) ≤ η / 2 :=
    dist_le_of_inner_cap hnegω hys hηhalf hy_cap
  have hy₂ : y ∈ {z | z ∈ sphere d ∧ (η / 2 - 1 : ℝ) ≤ ⟪z, α⟫} := by
    refine ⟨hys, ?_⟩
    -- ⟪α, y⟫ = ⟪α, -ω⟫ + ⟪α, y + ω⟫ ≥ (η - 1) - ‖y + ω‖
    have hsplit : (⟪α, y⟫ : ℝ) = ⟪α, -ω⟫ + ⟪α, y - -ω⟫ := by
      rw [inner_sub_right]; ring
    have hfirst : (⟪α, -ω⟫ : ℝ) = η - 1 := by
      rw [inner_neg_right, hη_def]; ring
    have hsecond : -(‖y - -ω‖) ≤ (⟪α, y - -ω⟫ : ℝ) := by
      have hcs := abs_real_inner_le_norm α (y - -ω)
      rw [hα, one_mul] at hcs
      linarith [(abs_le.mp hcs).1]
    have hnorm_le : ‖y - -ω‖ ≤ η / 2 := by
      rw [← dist_eq_norm]; exact hy_dist
    have : (η - 1) - η / 2 ≤ (⟪α, y⟫ : ℝ) := by
      rw [hsplit, hfirst]
      linarith
    rw [real_inner_comm]
    linarith
  have hz₁ := hMaps₂ hy₂
  set z := B₂.blockFlow T y with hz_def
  have hzs : z ∈ sphere d := B₂.blockFlow_mem_sphere hys hT.le
  -- the final cap sits inside the orthant
  have hz_cap : (1 - c ^ 2 / 8 : ℝ) ≤ ⟪α, z⟫ := by
    rw [real_inner_comm]
    exact hz₁
  show ∀ i, 0 < (flowMap [B₁, B₂] T x) i
  rw [hflow]
  exact cap_pos_coords hα hc hcoord hzs hz_cap

end MeasureToMeasure.Leaves
