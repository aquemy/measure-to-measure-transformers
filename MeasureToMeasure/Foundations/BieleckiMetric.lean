import MeasureToMeasure.Foundations.SphereProbIdOfIndiscernibles
import Mathlib.Topology.ContinuousMap.Compact

/-!
# The Bielecki-weighted metric on `C([0,T], SphereProb d)` (M3b existence, leaf E3a)

Toward `exists_meanFieldFlow` (M3b existence): the outer McKean-Vlasov self-consistency fixed point
(E3) needs `ContractingWith`, but the field's measure-Lipschitz constant
`‖V‖(e^{2‖B‖}+e^{4‖B‖})(1+‖B‖)` is not `< 1`, so the ordinary sup-metric Picard map on
`C([0,T], SphereProb d)` is not literally a contraction. The classical fix (Bielecki 1956) reweights
the metric by a decaying exponential in time, `d_λ(f,g) = sup_t e^{-λt}·dist(f_t,g_t)`, which turns
*any* finite Lipschitz constant into a contraction once `λ` is taken large enough, while leaving the
topology (hence completeness) unchanged.

This leaf builds `bieleckiDist` (and its weight `bieleckiWeight`) as a function on
`C(Set.Icc 0 T, SphereProb d)` and proves it is a genuine pseudometric (`dist_self`, `dist_comm`,
`dist_triangle`) **equivalent** to the ambient sup-metric `dist`:

  `bieleckiDist f g ≤ dist f g ≤ Real.exp (λ*T) * bieleckiDist f g`  (for `λ, T ≥ 0`).

The equivalence is what will let the *next* leaf package `bieleckiDist` as a genuine competing
`PseudoMetricSpace`/`MetricSpace` instance via `PseudoMetricSpace.replaceUniformity`
(same uniformity ⇒ same topology ⇒ `CompleteSpace` transfers for free from the ambient sup-metric
instance already banked via Mathlib's `C(α,β)` API for compact `α`), and to state the outer Picard
map's `ContractingWith` claim once the contraction exponent `λ` is pinned down by the field's
modulus.

M3b staging: consumed when `exists_meanFieldFlow` is discharged; see RESEARCH.md.
-/

open MeasureTheory Set

namespace MeasureToMeasure

variable {d : ℕ} {T lam : ℝ}

/-- The Bielecki weight `e^{-λt}` at time `t ∈ [0,T]`. -/
noncomputable def bieleckiWeight (t : Set.Icc (0 : ℝ) T) : ℝ := Real.exp (-lam * t.1)

theorem bieleckiWeight_pos (t : Set.Icc (0 : ℝ) T) :
    0 < bieleckiWeight (T := T) (lam := lam) t := by
  unfold bieleckiWeight; positivity

/-- The Bielecki weight is at most `1` for `t ≥ 0` and `λ ≥ 0`. -/
theorem bieleckiWeight_le_one (hlam : 0 ≤ lam) (t : Set.Icc (0 : ℝ) T) :
    bieleckiWeight (T := T) (lam := lam) t ≤ 1 := by
  unfold bieleckiWeight
  have hnn : (0 : ℝ) ≤ lam * t.1 := mul_nonneg hlam t.2.1
  calc Real.exp (-lam * t.1) ≤ Real.exp 0 := by apply Real.exp_le_exp.mpr; linarith
    _ = 1 := Real.exp_zero

/-- The Bielecki-weighted sup-distance on `C([0,T], SphereProb d)`:
`d_λ(f,g) = sup_{t∈[0,T]} e^{-λt}·dist(f_t,g_t)`. -/
noncomputable def bieleckiDist (f g : C(Set.Icc (0 : ℝ) T, SphereProb d)) : ℝ :=
  ⨆ t : Set.Icc (0 : ℝ) T, bieleckiWeight (lam := lam) t * dist (f t) (g t)

/-- The pointwise weighted distances are bounded above by the ambient sup-distance, uniformly:
`bieleckiWeight t · dist (f t) (g t) ≤ dist f g`. What makes `bieleckiDist` well-defined as a
supremum. -/
theorem bieleckiDist_bddAbove (hlam : 0 ≤ lam) (f g : C(Set.Icc (0 : ℝ) T, SphereProb d)) :
    BddAbove (Set.range (fun s : Set.Icc (0 : ℝ) T =>
      bieleckiWeight (lam := lam) s * dist (f s) (g s))) := by
  refine ⟨(dist f g : ℝ), ?_⟩
  rintro x ⟨s, rfl⟩
  have h1 := bieleckiWeight_le_one (T := T) (lam := lam) hlam s
  have hfs : (0 : ℝ) ≤ dist (f s) (g s) := dist_nonneg
  have hd : dist (f s) (g s) ≤ dist f g := ContinuousMap.dist_apply_le_dist s
  have hdfg : (0 : ℝ) ≤ dist f g := dist_nonneg
  nlinarith [hfs, hd, hdfg, h1]

theorem le_bieleckiDist (hlam : 0 ≤ lam) (f g : C(Set.Icc (0 : ℝ) T, SphereProb d))
    (t : Set.Icc (0 : ℝ) T) :
    bieleckiWeight (lam := lam) t * dist (f t) (g t) ≤ bieleckiDist (T := T) (lam := lam) f g :=
  le_ciSup (bieleckiDist_bddAbove hlam f g) t

/-- **`bieleckiDist` is dominated by the ambient sup-metric.** -/
theorem bieleckiDist_le_dist (hlam : 0 ≤ lam) (f g : C(Set.Icc (0 : ℝ) T, SphereProb d)) :
    bieleckiDist (T := T) (lam := lam) f g ≤ dist f g := by
  rcases isEmpty_or_nonempty (Set.Icc (0 : ℝ) T) with hE | hne
  · simp [bieleckiDist, Real.iSup_of_isEmpty]
  · apply ciSup_le
    intro t
    have h1 := bieleckiWeight_le_one (T := T) (lam := lam) hlam t
    have hft : (0 : ℝ) ≤ dist (f t) (g t) := dist_nonneg
    have hd : dist (f t) (g t) ≤ dist f g := ContinuousMap.dist_apply_le_dist t
    have hdfg : (0 : ℝ) ≤ dist f g := dist_nonneg
    nlinarith [hft, hd, hdfg, h1]

/-- **The ambient sup-metric is dominated by `bieleckiDist`, up to `e^{λT}`.** Together with
`bieleckiDist_le_dist` this is the equivalence `bieleckiDist ≤ dist ≤ e^{λT}·bieleckiDist`. -/
theorem dist_le_exp_mul_bieleckiDist (hlam : 0 ≤ lam) (hT : 0 ≤ T)
    (f g : C(Set.Icc (0 : ℝ) T, SphereProb d)) :
    dist f g ≤ Real.exp (lam * T) * bieleckiDist (T := T) (lam := lam) f g := by
  haveI hne : Nonempty (Set.Icc (0 : ℝ) T) := ⟨⟨0, le_refl 0, hT⟩⟩
  rw [ContinuousMap.dist_le_iff_of_nonempty]
  intro t
  have hle := le_bieleckiDist (T := T) (lam := lam) hlam f g t
  have hwpos := bieleckiWeight_pos (T := T) (lam := lam) t
  have hdnn : (0 : ℝ) ≤ dist (f t) (g t) := dist_nonneg
  have hwnn : (0 : ℝ) ≤ bieleckiWeight (T := T) (lam := lam) t * dist (f t) (g t) :=
    mul_nonneg hwpos.le hdnn
  have hBnn : (0 : ℝ) ≤ bieleckiDist (T := T) (lam := lam) f g := le_trans hwnn hle
  have hwinv : (bieleckiWeight (T := T) (lam := lam) t)⁻¹ ≤ Real.exp (lam * T) := by
    rw [inv_le_iff_one_le_mul₀ hwpos]
    unfold bieleckiWeight
    rw [mul_comm, ← Real.exp_add]
    have heq : -lam * t.1 + lam * T = lam * (T - t.1) := by ring
    rw [heq]
    have hnn : (0 : ℝ) ≤ lam * (T - t.1) := mul_nonneg hlam (by linarith [t.2.2])
    calc (1 : ℝ) = Real.exp 0 := (Real.exp_zero).symm
      _ ≤ Real.exp (lam * (T - t.1)) := Real.exp_le_exp.mpr hnn
  calc dist (f t) (g t)
      ≤ (bieleckiWeight (T := T) (lam := lam) t)⁻¹ * bieleckiDist (T := T) (lam := lam) f g := by
        rw [le_inv_mul_iff₀ hwpos, mul_comm]
        rwa [mul_comm] at hle
    _ ≤ Real.exp (lam * T) * bieleckiDist (T := T) (lam := lam) f g :=
        mul_le_mul_of_nonneg_right hwinv hBnn

theorem bieleckiDist_self (f : C(Set.Icc (0 : ℝ) T, SphereProb d)) :
    bieleckiDist (T := T) (lam := lam) f f = 0 := by
  unfold bieleckiDist; simp

theorem bieleckiDist_comm (f g : C(Set.Icc (0 : ℝ) T, SphereProb d)) :
    bieleckiDist (T := T) (lam := lam) f g = bieleckiDist (T := T) (lam := lam) g f := by
  unfold bieleckiDist; simp_rw [dist_comm (f _) (g _)]

/-- **Triangle inequality for `bieleckiDist`.** -/
theorem bieleckiDist_triangle (hlam : 0 ≤ lam) (f g h : C(Set.Icc (0 : ℝ) T, SphereProb d)) :
    bieleckiDist (T := T) (lam := lam) f h
      ≤ bieleckiDist (T := T) (lam := lam) f g + bieleckiDist (T := T) (lam := lam) g h := by
  rcases isEmpty_or_nonempty (Set.Icc (0 : ℝ) T) with hE | hne
  · simp [bieleckiDist, Real.iSup_of_isEmpty]
  · apply ciSup_le
    intro t
    have hwpos := (bieleckiWeight_pos (T := T) (lam := lam) t).le
    have htri : dist (f t) (h t) ≤ dist (f t) (g t) + dist (g t) (h t) := dist_triangle _ _ _
    have hmul : bieleckiWeight (T := T) (lam := lam) t * dist (f t) (h t)
        ≤ bieleckiWeight (T := T) (lam := lam) t * dist (f t) (g t)
          + bieleckiWeight (T := T) (lam := lam) t * dist (g t) (h t) := by
      have := mul_le_mul_of_nonneg_left htri hwpos
      linarith [this]
    have h1 := le_bieleckiDist (T := T) (lam := lam) hlam f g t
    have h2 := le_bieleckiDist (T := T) (lam := lam) hlam g h t
    linarith

end MeasureToMeasure
