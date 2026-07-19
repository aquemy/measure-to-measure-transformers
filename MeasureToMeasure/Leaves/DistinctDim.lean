import MeasureToMeasure.Statements.SupportedIn

/-!
# Leaf (Lemma 3.4 Part 1, Path I assembly): distinct measures force `2 ≤ d`

`lemma_3_4_part1` carries no dimension hypothesis, yet the App. B.3 collapse needs a genuine spherical
cap (a unit pole with room beside the cap direction), i.e. `2 ≤ d`. This leaf recovers `2 ≤ d` from the
*existence* of two distinct probability measures on `𝕊^{d-1} ∩ orthant`:

* `d = 0`: `Eucl 0` is a point with norm `0`, so `sphere 0 = ∅` and no probability measure can be
  supported on it — contradiction.
* `d = 1`: `sphere 1 ∩ orthant 1 = {p}` (the coordinate-`1` point), a **singleton**, so any two
  probability measures supported there are the Dirac at `p` — so `μ = ν`, contradicting `μ ≠ ν`.

Hence `2 ≤ d`.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory
open MeasureToMeasure.Statements (orthant)
open scoped RealInnerProductSpace

/-- Two probability measures supported on a subsingleton set agree (both are the Dirac at the point). -/
theorem eq_of_supported_subsingleton {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {S : Set α} (hSsub : S.Subsingleton) (hμS : μ Sᶜ = 0) (hνS : ν Sᶜ = 0) : μ = ν := by
  -- `S` is nonempty (else `μ univ = 0`), hence a singleton `{p}`
  rcases S.eq_empty_or_nonempty with hemp | ⟨p, hp⟩
  · exfalso
    rw [hemp, Set.compl_empty, measure_univ] at hμS
    exact one_ne_zero hμS
  have hSp : S = {p} := hSsub.eq_singleton_of_mem hp
  rw [hSp] at hμS hνS
  -- each measure puts full mass `1` on `{p}`
  have hmass : ∀ (ρ : Measure α) [IsProbabilityMeasure ρ], ρ {p}ᶜ = 0 → ρ {p} = 1 := by
    intro ρ _ h
    have hsum := measure_add_measure_compl (μ := ρ) (measurableSet_singleton p)
    rw [h, add_zero, measure_univ] at hsum
    exact hsum
  have hμp : μ {p} = 1 := hmass μ hμS
  have hνp : ν {p} = 1 := hmass ν hνS
  ext A hA
  -- off `{p}` there is no mass, so `ρ A = ρ (A ∩ {p})`
  have key : ∀ (ρ : Measure α) [IsProbabilityMeasure ρ], ρ {p}ᶜ = 0 → ρ A = ρ (A ∩ {p}) := by
    intro ρ _ hc
    refine measure_congr (ae_eq_set.mpr ⟨?_, ?_⟩)
    · refine measure_mono_null ?_ hc
      intro x hx
      rw [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hxp
      exact hx.2 ⟨hx.1, hxp⟩
    · rw [Set.sdiff_eq_empty.mpr Set.inter_subset_left]
      exact measure_empty
  by_cases hpA : p ∈ A
  · rw [key μ hμS, key ν hνS, Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr hpA), hμp, hνp]
  · rw [key μ hμS, key ν hνS, Set.inter_singleton_eq_empty.mpr hpA]; simp

variable {d : ℕ}

/-- **Distinct measures force `2 ≤ d`.** Two distinct probability measures on `𝕊^{d-1} ∩ orthant`
exist only when `2 ≤ d`: at `d = 0` the sphere is empty, and at `d = 1` the support is a single point
(forcing `μ = ν`). -/
theorem two_le_d_of_distinct {μ ν : Measure (Eucl d)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hne : μ ≠ ν) (hμs : μ (sphere d)ᶜ = 0) (hνs : ν (sphere d)ᶜ = 0)
    (hμo : μ (orthant d)ᶜ = 0) (hνo : ν (orthant d)ᶜ = 0) : 2 ≤ d := by
  by_contra hlt
  simp only [not_le] at hlt
  interval_cases d
  · -- `d = 0`: the sphere is empty, so `μ` cannot be a probability measure supported on it
    have hemp : sphere 0 = (∅ : Set (Eucl 0)) := by
      ext x
      simp only [sphere, Metric.mem_sphere, dist_zero_right, Set.mem_empty_iff_false, iff_false]
      rw [Subsingleton.elim x 0]; simp
    rw [hemp, Set.compl_empty, measure_univ] at hμs
    exact one_ne_zero hμs
  · -- `d = 1`: `sphere 1 ∩ orthant 1` is a singleton
    apply hne
    set S : Set (Eucl 1) := sphere 1 ∩ orthant 1 with hS
    -- on `Eucl 1`, `‖x‖ = |x 0|`, so sphere-∩-orthant pins `x 0 = 1`
    have hcoord : ∀ x : Eucl 1, x ∈ S → x 0 = 1 := by
      intro x hx
      obtain ⟨hxs, hxo⟩ := hx
      have hnx : ‖x‖ = |x 0| := by
        rw [EuclideanSpace.norm_eq]; simp [Real.sqrt_sq_eq_abs]
      have h1 : |x 0| = 1 := by rw [← hnx]; exact norm_eq_one_of_mem_sphere hxs
      have hpos : 0 < x 0 := hxo 0
      rwa [abs_of_pos hpos] at h1
    have hSsub : S.Subsingleton := by
      intro x hx y hy
      have hx0 := hcoord x hx
      have hy0 := hcoord y hy
      ext i
      rw [Subsingleton.elim i 0, hx0, hy0]
    have hμS : μ Sᶜ = 0 := by rw [hS, Set.compl_inter]; exact measure_union_null hμs hμo
    have hνS : ν Sᶜ = 0 := by rw [hS, Set.compl_inter]; exact measure_union_null hνs hνo
    exact eq_of_supported_subsingleton hSsub hμS hνS

end MeasureToMeasure.Leaves
