import MeasureToMeasure.Foundations.Sphere

/-!
# Leaf (Lemma 3.4 Part 1, Path I): a tight gate cap lies inside the carrier

The fixing clause of Lemma 3.4 asks that the constructed flow be the identity off the open carrier
`U` (`∀ x ∈ 𝕊, x ∉ U → flowMap θ T x = x`). The gated block fixes every point **off its gate cap**
(L2, `flowMap_gatedBlock_id_of_inner_le`: `⟪z, x⟫ ≤ cos R ⇒ flow fixes x`), so it suffices to place
the gate cap `{x ∈ 𝕊 | cos R < ⟪z, ·⟫}` *inside* `U`: then `x ∉ U` forces `x` off the cap, hence fixed.

This leaf is the topology that makes that placement possible. On unit vectors the cap is a metric-ball
trace — `‖x − z‖² = 2 − 2⟪z, x⟫`, so `cos R < ⟪z, x⟫ ⟺ ‖x − z‖ < √(2(1 − cos R))` — so pushing
`cos R → 1` shrinks the cap to `{z}`. Since `U` is an open neighbourhood of the unit direction `z`, some
`cos R < 1` (indeed `cos R ≥ 0`) makes the whole cap fit inside `U`.
-/

namespace MeasureToMeasure

open scoped RealInnerProductSpace

variable {d : ℕ}

/-- **Tight gate cap inside the carrier.** For a unit gate direction `z` in an open set `U`, some
threshold `cos R` with `0 ≤ cos R < 1` makes the sphere cap `{x ∈ 𝕊 | cos R < ⟪z, x⟫}` a subset of
`U`. Contrapositive (used by the fixing clause): a sphere point outside `U` has `⟪z, x⟫ ≤ cos R`, so
the gated block leaves it fixed. -/
theorem exists_cosR_cap_subset {z : Eucl d} (hz : ‖z‖ = 1) {U : Set (Eucl d)}
    (hU : IsOpen U) (hzU : z ∈ U) :
    ∃ cosR : ℝ, 0 ≤ cosR ∧ cosR < 1 ∧ ∀ x ∈ sphere d, cosR < (⟪z, x⟫ : ℝ) → x ∈ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU z hzU
  -- shrink the radius to at most `1` so the threshold stays in `[1/2, 1)`
  set ε' : ℝ := min ε 1 with hε'
  have hε'pos : 0 < ε' := lt_min hε one_pos
  have hε'le1 : ε' ≤ 1 := min_le_right _ _
  have hε'leε : ε' ≤ ε := min_le_left _ _
  refine ⟨1 - ε' ^ 2 / 2, by nlinarith, by nlinarith, fun x hx hxcap => ?_⟩
  have hxnorm : ‖x‖ = 1 := norm_eq_one_of_mem_sphere hx
  -- sphere polarization turns the cap threshold into a distance bound
  have hpol : ‖x - z‖ ^ 2 = 2 - 2 * (⟪z, x⟫ : ℝ) := by
    rw [norm_sub_sq_real, hxnorm, hz, real_inner_comm]; ring
  have hlt : ‖x - z‖ ^ 2 < ε' ^ 2 := by rw [hpol]; nlinarith
  have hdist : ‖x - z‖ < ε' := by
    have := abs_lt_of_sq_lt_sq hlt hε'pos.le
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  exact hball (by rw [Metric.mem_ball, dist_eq_norm]; exact hdist.trans_le hε'leε)

end MeasureToMeasure
