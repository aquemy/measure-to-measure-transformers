import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Leaf (`lemma_3_4_part2` non-vacuous re-discharge, group G4): off-span margin

Quantitative stability step replacing the refuted `hgenRest`/gramGap machinery (finding F22): turn
the pole's *qualitative* avoidance of a line (`∀ c, a ≠ c • β`) into a *positive margin*
(`0 < infDist a (span ℝ {β})`) that survives a small perturbation of `a`, e.g. the μ-side W2 error
in the Appendix B.3 asymmetric-cap route.

The statement uniformly covers the degenerate direction `β = 0`: then `span ℝ {β} = ⊥ = {0}`, the
hypothesis at `c = 0` gives `a ≠ 0`, and the margin is `infDist a {0} = ‖a‖ > 0`.

Proof shape: a finite-dimensional subspace of a real normed space is closed
(`Submodule.closed_of_finiteDimensional`), a point outside a nonempty closed set has positive
`infDist` (`IsClosed.notMem_iff_infDist_pos`), and the stability clause is one triangle-style
inequality: if `b' = γ • β` then `b' ∈ span ℝ {β}`, so `infDist a (span ℝ {β}) ≤ dist a b'`,
contradicting `dist b' a < infDist a (span ℝ {β})`.

Deliberately proved over an ABSTRACT `[NormedAddCommGroup E] [NormedSpace ℝ E]
[FiniteDimensional ℝ E]`, not `Eucl d`, in a file with no `Eucl`-touching import, per this repo's
known elaboration-timeout gotcha (see `Leaves/UniformRadiusPacking.lean`). Callers needing `Eucl d`
should `apply` this theorem, not re-elaborate it with `Eucl d` in scope.
-/

namespace MeasureToMeasure.Leaves

/-- **Off-span margin with stability.** If `a` is not a scalar multiple of `β` (equivalently, `a`
lies off the line `span ℝ {β}`, including the `β = 0` case where the line degenerates to `{0}`),
then `a` keeps a positive distance `infDist a (span ℝ {β})` from that line, and every point `b'`
strictly within that margin of `a` is itself not a scalar multiple of `β`. -/
theorem forall_ne_smul_of_dist_lt_infDist_span
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {a β : E} (ha : ∀ c : ℝ, a ≠ c • β) :
    0 < Metric.infDist a (Submodule.span ℝ {β} : Set E) ∧
      ∀ b' : E, dist b' a < Metric.infDist a (Submodule.span ℝ {β} : Set E) →
        ∀ γ : ℝ, b' ≠ γ • β := by
  have hclosed : IsClosed (Submodule.span ℝ {β} : Set E) :=
    (Submodule.span ℝ {β}).closed_of_finiteDimensional
  have hnotmem : a ∉ (Submodule.span ℝ {β} : Set E) := by
    intro hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    exact ha c hc.symm
  have hpos : 0 < Metric.infDist a (Submodule.span ℝ {β} : Set E) :=
    (hclosed.notMem_iff_infDist_pos ⟨0, Submodule.zero_mem _⟩).mp hnotmem
  refine ⟨hpos, ?_⟩
  intro b' hb' γ hb'eq
  have hmem' : b' ∈ (Submodule.span ℝ {β} : Set E) :=
    Submodule.mem_span_singleton.mpr ⟨γ, hb'eq.symm⟩
  have hle : Metric.infDist a (Submodule.span ℝ {β} : Set E) ≤ dist a b' :=
    Metric.infDist_le_dist_of_mem hmem'
  rw [dist_comm] at hb'
  linarith

end MeasureToMeasure.Leaves
