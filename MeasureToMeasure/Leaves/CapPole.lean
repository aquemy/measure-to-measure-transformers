import MeasureToMeasure.Foundations.Sphere

/-!
# Leaf (Lemma 3.4 Part 1, Path I assembly): a pole strictly inside the cap, off one point

The App. B.3 collapse pole `ω = x*` is chosen by the pigeonhole to *separate* the two collapsed
barycenters: any `ω` off the single forced vector `v = c⁻¹(∫_{capᶜ}(ν−μ))` works. But `ω` must be a
**unit** vector strictly inside the gate cap `{cos R < ⟪z, ·⟫}`, so the Euclidean-ball pigeonhole of
L3a does not directly apply — the pole ranges over a *spherical* cap.

This leaf supplies the missing geometry: given a unit `w ⊥ z`, the two rotations
`ω± = c·z ± s·w` (with `c = (1+cos R)/2 ∈ (cos R, 1)`, `s = √(1−c²) > 0`) are **distinct** unit vectors
both strictly inside the cap (`⟪z, ω±⟫ = c > cos R`). Two distinct points cannot both equal `v`, so one
of them is the pole. The unit `w ⊥ z` exists exactly when `2 ≤ d` (supplied by the assembly, which
derives it from `μ ≠ ν`).
-/

namespace MeasureToMeasure.Leaves

open scoped RealInnerProductSpace

variable {d : ℕ}

/-- **Spherical-cap pigeonhole for the pole.** Given a unit `w` orthogonal to the unit cap direction
`z`, and any forbidden vector `v`, there is a unit vector `ω` strictly inside the cap
`{cos R < ⟪z, ·⟫}` with `ω ≠ v`. Realised by the two cap rotations `c·z ± s·w`, which are distinct unit
vectors with `⟪z, ·⟫ = c > cos R`; at most one equals `v`. -/
theorem exists_pole_in_cap_ne {z w : Eucl d} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (hzw : (⟪z, w⟫ : ℝ) = 0) {cosR : ℝ} (hcosRlb : -1 ≤ cosR) (hcosR : cosR < 1) (v : Eucl d) :
    ∃ ω : Eucl d, ‖ω‖ = 1 ∧ cosR < (⟪z, ω⟫ : ℝ) ∧ ω ≠ v := by
  set c : ℝ := (1 + cosR) / 2 with hc
  have hc_lt : cosR < c := by rw [hc]; linarith
  have hc1 : c < 1 := by rw [hc]; linarith
  have hc0 : 0 ≤ c := by rw [hc]; linarith
  set s : ℝ := Real.sqrt (1 - c ^ 2) with hs
  have hs2 : s ^ 2 = 1 - c ^ 2 := Real.sq_sqrt (by nlinarith)
  have hspos : 0 < s := Real.sqrt_pos.mpr (by nlinarith)
  have hzz : (⟪z, z⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hz]; norm_num
  have hww : (⟪w, w⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  have hwz : (⟪w, z⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact hzw
  -- the two cap rotations are unit vectors (using `ε² = 1 − c²`)
  have hnorm : ∀ ε : ℝ, ε ^ 2 = 1 - c ^ 2 → ‖c • z + ε • w‖ = 1 := by
    intro ε hε
    have hsq : ‖c • z + ε • w‖ ^ 2 = c ^ 2 + ε ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
        hzz, hww, hzw, hwz]
      ring
    calc ‖c • z + ε • w‖ = Real.sqrt (‖c • z + ε • w‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt 1 := by rw [hsq, hε]; ring_nf
      _ = 1 := Real.sqrt_one
  -- and lie strictly inside the cap
  have hinner : ∀ ε : ℝ, (⟪z, c • z + ε • w⟫ : ℝ) = c := by
    intro ε
    simp only [inner_add_right, real_inner_smul_right, hzz, hzw]; ring
  -- the two rotations are distinct (differ by `2s • w`, `s > 0`, `w ≠ 0`)
  have hwne : w ≠ 0 := fun h => by simp [h] at hw
  have hdistinct : c • z + s • w ≠ c • z + (-s) • w := by
    intro h
    have h2 : s • w = (-s) • w := add_left_cancel h
    rw [neg_smul, eq_neg_iff_add_eq_zero, ← add_smul, smul_eq_zero] at h2
    rcases h2 with h1 | h1
    · linarith [hspos]
    · exact hwne h1
  have hnegs2 : (-s) ^ 2 = 1 - c ^ 2 := by rw [neg_pow]; simpa using hs2
  -- at most one rotation equals `v`
  by_cases hv : c • z + s • w = v
  · exact ⟨c • z + (-s) • w, hnorm _ hnegs2, by rw [hinner]; exact hc_lt,
      fun h => hdistinct (hv.trans h.symm)⟩
  · exact ⟨c • z + s • w, hnorm _ hs2, by rw [hinner]; exact hc_lt, hv⟩

end MeasureToMeasure.Leaves
