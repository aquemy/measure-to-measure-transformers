import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import MeasureToMeasure.Foundations.Sphere

/-!
# Leaf (Lemma 3.4 Part 1, Path I assembly): a mass-gap ball centred in a co-null target set

`exists_closedBall_measure_ne` (L3-ball) locates *some* ball on which two distinct measures differ,
but the App. B.3 collapse needs the ball centred where the mass actually lives — on the sphere, inside
the carrier `U`. This leaf strengthens the Besicovitch argument to place the differentiation point in
**any** target set `W` that is co-null for `ρ = μ + ν` (in the assembly `W = U ∩ 𝕊`), and to give the
mass gap on **all sufficiently small** balls, not just one.

The mechanism is the same Radon–Nikodym differentiation against `ρ = μ + ν` used in L3-ball. If `μ ≠ ν`
their densities `μ.rnDeriv ρ`, `ν.rnDeriv ρ` disagree on a set of positive `ρ`-measure; intersecting
with the co-null `W` and the full-measure Besicovitch convergence set leaves a point `z ∈ W` where the
closed-ball ratios `μ(closedBall z r)/ρ(...)`, `ν(closedBall z r)/ρ(...)` tend to **distinct** limits.
Distinct limits are eventually separated (Hausdorff), so `μ(closedBall z r) ≠ ν(closedBall z r)` for all
small `r`.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Metric Filter Topology
open scoped ENNReal

variable {d : ℕ}

/-- **Mass-gap ball centred in a co-null target set.** If `μ ≠ ν` are finite and `W` is co-null for
`μ + ν`, some centre `z ∈ W` has `μ (closedBall z r) ≠ ν (closedBall z r)` for every sufficiently small
`r`. Besicovitch differentiation against `ρ = μ + ν`, with the differentiation point pinned into `W`. -/
theorem exists_mem_eventually_closedBall_measure_ne {μ ν : Measure (Eucl d)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hne : μ ≠ ν)
    {W : Set (Eucl d)} (hW : (μ + ν) Wᶜ = 0) :
    ∃ z ∈ W, ∀ᶠ r in 𝓝[>] (0 : ℝ), μ (closedBall z r) ≠ ν (closedBall z r) := by
  set ρ : Measure (Eucl d) := μ + ν with hρ
  have hμρ : μ ≪ ρ := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hνρ : ν ≪ ρ := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  have hμ_ae := Besicovitch.ae_tendsto_rnDeriv μ ρ
  have hν_ae := Besicovitch.ae_tendsto_rnDeriv ν ρ
  have hWae : ∀ᵐ x ∂ρ, x ∈ W := by rw [ae_iff]; exact hW
  -- extract a density-disagreement point that lies in `W` and enjoys both convergences
  have hexists : ∃ z, z ∈ W ∧
      Tendsto (fun r => μ (closedBall z r) / ρ (closedBall z r)) (𝓝[>] 0)
        (𝓝 (μ.rnDeriv ρ z)) ∧
      Tendsto (fun r => ν (closedBall z r) / ρ (closedBall z r)) (𝓝[>] 0)
        (𝓝 (ν.rnDeriv ρ z)) ∧
      μ.rnDeriv ρ z ≠ ν.rnDeriv ρ z := by
    by_contra hcon
    refine hne ?_
    have heq : μ.rnDeriv ρ =ᵐ[ρ] ν.rnDeriv ρ := by
      filter_upwards [hWae, hμ_ae, hν_ae] with x hxW hxμ hxν
      by_contra hxdiff
      exact hcon ⟨x, hxW, hxμ, hxν, hxdiff⟩
    calc μ = ρ.withDensity (μ.rnDeriv ρ) := (Measure.withDensity_rnDeriv_eq μ ρ hμρ).symm
      _ = ρ.withDensity (ν.rnDeriv ρ) := withDensity_congr_ae heq
      _ = ν := Measure.withDensity_rnDeriv_eq ν ρ hνρ
  obtain ⟨z, hzW, hzμ, hzν, hzne⟩ := hexists
  refine ⟨z, hzW, ?_⟩
  -- distinct limits are eventually separated, so the ratios (hence the masses) eventually differ
  have hprod := hzμ.prodMk_nhds hzν
  have hopen : IsOpen {p : ℝ≥0∞ × ℝ≥0∞ | p.1 ≠ p.2} := isClosed_diagonal.isOpen_compl
  have hev := hprod.eventually (hopen.mem_nhds hzne)
  filter_upwards [hev] with r hr hmass
  exact hr (by simp only [hmass])

end MeasureToMeasure.Leaves
