import MeasureToMeasure.Foundations.SphereRounding
import MeasureToMeasure.Foundations.SphereMeasureBridge

/-!
# Finite-range value rounding of an a.e. sphere-valued map (lemma_5_4 campaign, G3)

The reduction that removes the "universal approximation" framing from `lemma_5_4`'s target map:
round a measurable, a.e. sphere-valued `ψ : Eucl d → Eucl d`'s VALUES (not its domain) through a
finite small-diameter partition of the target sphere, picking cell representatives. Preimages of
value-cells are measurable because `ψ` is, so the approximant is measurable with finite range,
sphere-valued range, and sup-norm a.e. error `≤ δ`. No Lusin machinery is needed for this step.

* `exists_finite_range_sphere_approx` — for a probability `μ`, a measurable `ψ` with
  `ψ x ∈ sphere d` for `μ`-a.e. `x`, and `δ > 0`: a measurable `ψ'` whose range lies in a finite
  set `s` of sphere points, with `‖ψ x - ψ' x‖ ≤ δ` for `μ`-a.e. `x`.

Construction: feed the pushforward `μ.map ψ` to `exists_finite_rounding` (its statement is
measure-relative, so the target-side measure is exactly what it wants) at scale `ε = δ/2`, and set
`ψ' x := g (sel (ψ x))` for the resulting measurable selection `sel : Eucl d → Fin M` and sphere
representatives `g : Fin M → Eucl d`. The finite range is `Finset.image g Finset.univ`, and the
`μ`-null-frontier clause of `exists_finite_rounding` is simply not consumed here: only finiteness
and the `< 2ε` displacement are load-bearing for this leaf.
-/

open MeasureTheory Metric Set

namespace MeasureToMeasure.Leaves

variable {d : ℕ}

/-- **Finite-range sphere-valued approximation by value rounding.** Any measurable, `μ`-a.e.
sphere-valued map `ψ` admits, for every `δ > 0`, a measurable approximant `ψ'` taking values in a
finite set of sphere points with a.e. error `‖ψ x - ψ' x‖ ≤ δ`. Obtained by applying the sphere
cell-rounding `exists_finite_rounding` to the pushforward `μ.map ψ` at scale `δ/2` and composing
the resulting rounding map with `ψ`. -/
theorem exists_finite_range_sphere_approx (μ : Measure (Eucl d)) [IsProbabilityMeasure μ]
    (ψ : Eucl d → Eucl d) (hm : Measurable ψ)
    (hs : ∀ᵐ x ∂μ, ψ x ∈ sphere d) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (ψ' : Eucl d → Eucl d) (s : Finset (Eucl d)),
      (∀ z ∈ s, z ∈ sphere d) ∧ (∀ x, ψ' x ∈ s) ∧ Measurable ψ' ∧
      (∀ᵐ x ∂μ, ‖ψ x - ψ' x‖ ≤ δ) := by
  classical
  -- The pushforward `μ.map ψ` is a sphere-supported probability measure.
  have hprob : IsProbabilityMeasure (μ.map ψ) :=
    ⟨by rw [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ, measure_univ]⟩
  have hν0 : (μ.map ψ) (sphere d)ᶜ = 0 := by
    rw [Measure.map_apply hm (measurableSet_sphere d).compl]
    have h2 : ψ ⁻¹' (sphere d)ᶜ = {a | ψ a ∉ sphere d} := rfl
    rw [h2]
    exact (MeasureTheory.ae_iff).mp hs
  -- Round the target sphere at scale `δ/2`, so the displacement bound `< 2 · (δ/2)` gives `≤ δ`.
  obtain ⟨M, sel, g, hsel, hg_sphere, hclose, _hfront⟩ :=
    exists_finite_rounding (μ.map ψ) hν0 (ε := δ / 2) (by positivity)
  refine ⟨fun x => g (sel (ψ x)), Finset.image g Finset.univ, ?_, ?_, ?_, ?_⟩
  · -- Every candidate value is a sphere point.
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hz
    exact hg_sphere i
  · -- The approximant's range lies in the finite set.
    intro x
    exact Finset.mem_image_of_mem g (Finset.mem_univ _)
  · -- Measurable: `g` is measurable out of the countable discrete `Fin M`.
    exact (measurable_of_countable g).comp (hsel.comp hm)
  · -- A.e. error: off the null off-sphere set, `ψ x` moves by `< 2 · (δ/2) = δ`.
    filter_upwards [hs] with x hx
    have hlt := hclose (ψ x) hx
    rw [← dist_eq_norm]
    linarith

end MeasureToMeasure.Leaves
