import Mathlib.Data.Fintype.Defs
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card

/-!
# Leaf 5, Phase-4 packaging: uniform radius from pairwise-distinct points

`exists_disentangling_balls`' final packaging step (Phase 4 of the induction, per the
`exists-disentangling-balls-campaign` project notes) needs to convert a family of pairwise-distinct
points into a UNIFORM radius `r ∈ (0,1)` with pairwise distance `≥ 2r` -- the `Metric.ball (α i) r`
/ `2r`-separation shape the axiom itself needs.

Deliberately stated over an ABSTRACT `[MetricSpace E]`, not `Eucl d`, and in a file importing NO
project-specific `Eucl d`-touching content: `Eucl d = EuclideanSpace ℝ (Fin d)`'s `MetricSpace`
instance (via `PiLp`) is definitionally heavy enough that elaborating `Finset.inf'_le`-style implicit
unification INSIDE this proof times out when `Eucl d`'s instances are in scope, even though the exact
same proof is fast over a fully abstract space. Callers needing the `Eucl d` (or unit-vector) case
should APPLY this already-proven theorem (a cheap term-mode instantiation), not re-elaborate its
tactic proof with `Eucl d` in scope.
-/

namespace MeasureToMeasure.Leaves

open Metric

/-- Given finitely many PAIRWISE-DISTINCT points in a bounded (diameter `≤ 2`) family, there's a
uniform `r ∈ (0,1)` with pairwise distance `≥ 2r`. -/
theorem exists_uniform_radius_of_pairwise_ne {E : Type*} [MetricSpace E] {ι : Type*} [Fintype ι]
    [Nonempty ι] (α : ι → E) (hbound : ∀ i j, dist (α i) (α j) ≤ 2)
    (hne : Pairwise fun i j => α i ≠ α j) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ i j, i ≠ j → 2 * r ≤ dist (α i) (α j) := by
  classical
  by_cases hcard : 1 < Fintype.card ι
  · obtain ⟨i₀, j₀, hij₀⟩ := Fintype.exists_pair_of_one_lt_card hcard
    have hpairs : ((Finset.univ ×ˢ Finset.univ : Finset (ι × ι)).filter
        (fun p => p.1 ≠ p.2)).Nonempty :=
      ⟨(i₀, j₀), by rw [Finset.mem_filter]; exact ⟨by rw [Finset.mem_product]; simp, hij₀⟩⟩
    set gap : ℝ := (((Finset.univ ×ˢ Finset.univ : Finset (ι × ι)).filter
        (fun p => p.1 ≠ p.2)).inf' hpairs (fun p => dist (α p.1) (α p.2))) with hgapdef
    have hgappos : 0 < gap := by
      rw [hgapdef]
      apply (Finset.lt_inf'_iff hpairs).mpr
      intro p hp
      rw [Finset.mem_filter] at hp
      exact dist_pos.mpr (hne hp.2)
    have hgaple2 : gap ≤ 2 := by
      calc gap ≤ dist (α i₀) (α j₀) := by
            rw [hgapdef]
            refine Finset.inf'_le (fun p => dist (α p.1) (α p.2)) (b := (i₀, j₀)) ?_
            rw [Finset.mem_filter]; exact ⟨by rw [Finset.mem_product]; simp, hij₀⟩
        _ ≤ 2 := hbound i₀ j₀
    refine ⟨gap / 4, by linarith, by linarith, fun i j hij => ?_⟩
    have hgple : gap ≤ dist (α i) (α j) := by
      rw [hgapdef]
      refine Finset.inf'_le (fun p => dist (α p.1) (α p.2)) (b := (i, j)) ?_
      rw [Finset.mem_filter]; exact ⟨by rw [Finset.mem_product]; simp, hij⟩
    linarith
  · refine ⟨1 / 2, by norm_num, by norm_num, fun i j hij => ?_⟩
    have hsub : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    exact absurd (Subsingleton.elim i j) hij

end MeasureToMeasure.Leaves
