import MeasureToMeasure.Leaves.CapSubset
import MeasureToMeasure.Statements.SupportedIn
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# A statically-chosen asymmetric cap: `A`-positive trace inside an open carrier, clear of a closed bad set

Group A-static-cap of the `exists_disentangling_balls` re-base. The kernel-refuted dynamic
`GenRestNearBall` gate (see `Leaves/GenRestNearBall.lean` and finding F22) tried to place a cap by
following the flow; this leaf replaces that with pure static point-set topology. Given a
sphere-supported probability measure `A` carried by an open set `W`, and a closed bad set `K` that
misses at least one support point of `A`, we produce a unit direction `z` and a threshold
`cosR ∈ (1/2, 1)` such that the inner-product cap `{cosR < ⟪z, ·⟫}` carries positive `A`-mass while
its whole SPHERE-TRACE stays inside `W` and clear of `K`.

**Proof route.** The excluded support point `x0` has a metric ball clear of the closed `K`. That
ball carries positive `A`-mass (`Measure.mem_support_iff_forall`); subtracting the `A`-null `Wᶜ`
keeps the mass positive, and a positive-measure set meets `A.support`
(`Measure.nonempty_inter_support_of_pos`), giving a support point `x1 ∈ ball ∩ W ∩ Kᶜ`. Take
`z := x1` (a unit vector, since `A.support` sits inside the closed sphere): on unit vectors
`‖x − z‖² = 2 − 2⟪z, x⟫`, so pushing `cosR → 1` shrinks the cap's sphere-trace into any open
neighborhood of `x1` (`exists_cosR_cap_subset` applied to `W ∩ Kᶜ`), and the cap itself is an open
neighborhood of `x1 ∈ A.support`, hence `A`-positive.

No dynamics, no axioms: the cap is chosen ONCE, before any flow runs, which is exactly what the
static re-base of the induction over `N` needs.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory MeasureToMeasure.Statements
open scoped RealInnerProductSpace

variable {d : ℕ}

/-- **Static cap placement.** For a sphere-supported probability measure `A` carried by an open
set `W`, and a closed set `K` missing at least one `A`-support point, there is a unit direction `z`
and a threshold `cosR ∈ (1/2, 1)` whose cap `{cosR < ⟪z, ·⟫}` has positive `A`-mass and whose
sphere-trace lies inside `W` and avoids `K`. -/
theorem exists_static_cap_in_open_avoiding_closed [NeZero d]
    (A : Measure (Eucl d)) [IsProbabilityMeasure A]
    (hAs : supportedIn A (sphere d))
    (W : Set (Eucl d)) (hWopen : IsOpen W) (hAW : supportedIn A W)
    (K : Set (Eucl d)) (hK : IsClosed K)
    (hexcl : ∃ x0, x0 ∈ A.support ∧ x0 ∉ K) :
    ∃ (z : Eucl d) (cosR : ℝ), ‖z‖ = 1 ∧ cosR ∈ Set.Ioo (1 / 2 : ℝ) 1 ∧
      0 < A {x | cosR < (⟪z, x⟫ : ℝ)} ∧
      (∀ x ∈ sphere d, cosR < (⟪z, x⟫ : ℝ) → x ∈ W ∧ x ∉ K) := by
  obtain ⟨x0, hx0supp, hx0K⟩ := hexcl
  -- a metric ball around `x0` clear of the closed `K`
  obtain ⟨δ, hδpos, hballK⟩ := Metric.isOpen_iff.mp hK.isOpen_compl x0 hx0K
  -- the ball carries positive `A`-mass, and stays positive after removing the `A`-null `Wᶜ`
  have hballpos : 0 < A (Metric.ball x0 δ) :=
    (Measure.mem_support_iff_forall x0).mp hx0supp _ (Metric.ball_mem_nhds x0 hδpos)
  have hposU : 0 < A (Metric.ball x0 δ ∩ W) := by
    refine pos_iff_ne_zero.mpr fun h0 => hballpos.ne' ?_
    have hsub : Metric.ball x0 δ ⊆ (Metric.ball x0 δ ∩ W) ∪ Wᶜ := by
      intro x hx
      by_cases hxW : x ∈ W
      · exact Or.inl ⟨hx, hxW⟩
      · exact Or.inr hxW
    exact measure_mono_null hsub (measure_union_null h0 hAW)
  -- a support point inside `ball ∩ W ∩ Kᶜ`
  obtain ⟨x1, ⟨hx1ball, hx1W⟩, hx1supp⟩ := Measure.nonempty_inter_support_of_pos hposU
  have hx1sphere : x1 ∈ sphere d :=
    Measure.support_subset_of_isClosed Metric.isClosed_sphere hAs hx1supp
  have hx1norm : ‖x1‖ = 1 := norm_eq_one_of_mem_sphere hx1sphere
  -- shrink the cap's sphere-trace into the open carrier `W ∩ Kᶜ` around `x1`
  have hUopen : IsOpen (W ∩ Kᶜ) := hWopen.inter hK.isOpen_compl
  have hx1U : x1 ∈ W ∩ Kᶜ := ⟨hx1W, hballK hx1ball⟩
  obtain ⟨cosR0, _hcosR0_nonneg, hcosR0_lt1, htrace0⟩ :=
    MeasureToMeasure.exists_cosR_cap_subset hx1norm hUopen hx1U
  refine ⟨x1, max cosR0 (3 / 4), hx1norm, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  · exact max_lt hcosR0_lt1 (by norm_num)
  · -- cap positivity: the cap is an open neighborhood of `x1 ∈ A.support`
    have hcapopen : IsOpen {x : Eucl d | max cosR0 (3 / 4) < (⟪x1, x⟫ : ℝ)} :=
      isOpen_lt continuous_const (continuous_const.inner continuous_id)
    have hx1cap : x1 ∈ {x : Eucl d | max cosR0 (3 / 4) < (⟪x1, x⟫ : ℝ)} := by
      have hself : (⟪x1, x1⟫ : ℝ) = 1 := by
        rw [real_inner_self_eq_norm_sq, hx1norm]; norm_num
      simp only [Set.mem_setOf_eq, hself]
      exact max_lt hcosR0_lt1 (by norm_num)
    exact (Measure.mem_support_iff_forall x1).mp hx1supp _ (hcapopen.mem_nhds hx1cap)
  · -- trace containment: bumping the threshold only shrinks the cap
    intro x hx hxcap
    exact htrace0 x hx (lt_of_le_of_lt (le_max_left _ _) hxcap)

/-- **Cap nullity from trace exclusivity.** If a sphere-supported measure `ν` has no support point
in the cap's sphere-trace, the whole cap is `ν`-null: the cap splits into its sphere-trace, which
misses `ν.support` and is hence contained in the null `ν.supportᶜ`, and an off-sphere part inside
the null `(sphere d)ᶜ`. This converts the `A`-side exclusivity delivered by
`exists_static_cap_in_open_avoiding_closed` into the `hνcap` input of
`exists_asymmetric_collapse_schedule`, for the `B`-side and for every bystander supported in the
bad set `K`. -/
theorem measure_cap_null_of_trace_disjoint_support
    (ν : Measure (Eucl d)) (hνs : supportedIn ν (sphere d))
    {z : Eucl d} {cosR : ℝ}
    (hdisj : ∀ x ∈ sphere d, cosR < (⟪z, x⟫ : ℝ) → x ∉ ν.support) :
    ν {x | cosR < (⟪z, x⟫ : ℝ)} = 0 := by
  have hsub : {x : Eucl d | cosR < (⟪z, x⟫ : ℝ)} ⊆ ν.supportᶜ ∪ (sphere d)ᶜ := by
    intro x hx
    by_cases hxs : x ∈ sphere d
    · exact Or.inl (hdisj x hxs hx)
    · exact Or.inr hxs
  exact measure_mono_null hsub (measure_union_null Measure.measure_compl_support hνs)

end MeasureToMeasure.Leaves
