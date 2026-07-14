import MeasureToMeasure.Foundations.AttnStepExistence
import Mathlib.MeasureTheory.Measure.Support

/-!
# Support under a continuous pushforward, and the closed-support-ball reduction

`lemma_3_4_part2` leaf 6 (`MidLevel.lean:267` sub-campaign, see `mean-field-axioms-retractability`
project notes). The paper's App. B.3 (B.16) conclusion is "some open ball meets `supp ν(T*)` but is
disjoint from `supp μ(T*)`" -- a local witness that some point of `ν`'s time-`T*` support has left
the (closed) set `supp μ(T*)`. This file supplies the two generic pieces the campaign's next steps
need to work with that conclusion directly as a POINT-SET claim, without re-deriving ball/topology
facts at every use site:

* **The closed-support-ball reduction**: `Measure.support` is always closed
  (`Measure.isClosed_support`), so "(B.16)'s ball" is EQUIVALENT to the pure point-set fact
  `∃ z ∈ supp ν, z ∉ supp μ` -- a point outside a closed set trivially has an open neighborhood
  disjoint from it. No continuity/flow argument is needed for this half.
* **Support under a continuous map**: `attnStep_exists_map`/`attnMeasureFlow_exists_map`
  (`AttnStepExistence.lean`) already export the transport map's own continuity (added alongside
  this leaf, specifically for this use). Two one-directional facts, each proved directly rather
  than via a combined `support (μ.map Φ) = Φ '' support μ` equality (the campaign's actual use
  needs the two directions for two DIFFERENT purposes, not both at once): a support point's image
  is a support point of the pushforward (continuity alone, no compactness), and the pushforward's
  support is contained in the image of the original support (needs the original support compact,
  so its continuous image is closed).

Neither of these is Voronoi/relay-specific or attention-specific -- they're generic measure-theory
facts about `Eucl d`, kept here (not `Foundations/`) because they're staged for this one campaign's
consumption, matching this repo's `Leaves/` convention for "used by exactly one downstream
discharge, not yet promoted to shared infrastructure."
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Set MeasureToMeasure

variable {d : ℕ}

/-- **A continuous pushforward sends support points to support points.** No compactness needed:
if `x` is in the topological support of `μ`, every open neighborhood of `x` has positive `μ`-mass,
and continuity pulls back neighborhoods of `Φ x` to neighborhoods of `x`. -/
theorem mem_support_map_of_continuous {μ : Measure (Eucl d)}
    {Φ : Eucl d → Eucl d} (hΦm : Measurable Φ) (hΦc : Continuous Φ)
    {x : Eucl d} (hx : x ∈ μ.support) :
    Φ x ∈ (μ.map Φ).support := by
  by_contra hcon
  have hUopen : IsOpen (μ.map Φ).supportᶜ := Measure.isOpen_compl_support
  have hpreopen : IsOpen (Φ ⁻¹' (μ.map Φ).supportᶜ) := hΦc.isOpen_preimage _ hUopen
  have hnull : μ (Φ ⁻¹' (μ.map Φ).supportᶜ) = 0 := by
    rw [← Measure.map_apply hΦm hUopen.measurableSet]
    exact Measure.measure_compl_support (μ := μ.map Φ)
  have hsub := Measure.subset_compl_support_of_isOpen hpreopen hnull
  exact hsub hcon hx

/-- **The pushforward's support is contained in the image of the original support**, when the
original support is compact (its continuous image is then closed, and a measure's support is the
smallest closed set carrying full measure). This is the direction that lets a point OUTSIDE
`Φ '' support μ` be certified outside `support (μ.map Φ)` too -- the tool for showing a candidate
witness point has genuinely left a flowed support, not just some enclosing set. -/
theorem support_map_subset_image_of_continuous {μ : Measure (Eucl d)}
    {Φ : Eucl d → Eucl d} (hΦm : Measurable Φ) (hΦc : Continuous Φ)
    (hcompact : IsCompact μ.support) :
    (μ.map Φ).support ⊆ Φ '' μ.support := by
  have himgclosed : IsClosed (Φ '' μ.support) := (hcompact.image hΦc).isClosed
  have hUopen : IsOpen (Φ '' μ.support)ᶜ := himgclosed.isOpen_compl
  have hnull : (μ.map Φ) (Φ '' μ.support)ᶜ = 0 := by
    rw [Measure.map_apply hΦm hUopen.measurableSet]
    apply measure_mono_null (fun x hx => ?_) (Measure.measure_compl_support (μ := μ))
    simp only [Set.mem_preimage, Set.mem_compl_iff] at hx ⊢
    exact fun hxs => hx ⟨x, hxs, rfl⟩
  have := Measure.subset_compl_support_of_isOpen hUopen hnull
  exact compl_subset_compl.mp this

/-- **The closed-support-ball reduction.** Since `Measure.support` is always closed, "some open
ball meets `supp ν` but is disjoint from `supp μ`" -- the paper's (B.16) conclusion -- is
EQUIVALENT to the pure point-set claim "some point of `supp ν` avoids `supp μ`": a point outside a
closed set has an open neighborhood disjoint from it, for free. -/
theorem exists_ball_meets_disjoint_of_exists_mem_not_mem {μ ν : Measure (Eucl d)}
    {z : Eucl d} (hzν : z ∈ ν.support) (hzμ : z ∉ μ.support) :
    ∃ ε > (0 : ℝ), z ∈ Metric.ball z ε ∧ (Metric.ball z ε ∩ μ.support) = ∅ ∧
      Metric.ball z ε ∩ ν.support ≠ ∅ := by
  have hclosed : IsClosed μ.support := Measure.isClosed_support
  obtain ⟨ε, hεpos, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl z hzμ
  refine ⟨ε, hεpos, Metric.mem_ball_self hεpos, ?_, ?_⟩
  · ext y
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hyball hyμ
    exact hball hyball hyμ
  · exact Set.nonempty_iff_ne_empty.mp ⟨z, Metric.mem_ball_self hεpos, hzν⟩

end MeasureToMeasure.Leaves
