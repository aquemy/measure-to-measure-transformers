import MeasureToMeasure.Foundations.DiscreteTV
import MeasureToMeasure.Foundations.SphereCover

/-!
# Cell total variation vanishes under weak convergence (M3b existence, leaf S3b-iv-glue-tv)

The portmanteau half of the `weak ⇒ W₁` crux (leaf S3b, toward `exists_meanFieldFlow`). Given a
measurable finite cell map `sel : Eucl d → Fin M` all of whose cells `sel ⁻¹' {i}` are
`μ`-continuity sets (`μ`-null frontier), weak convergence `μs → μ` forces the pushed-forward total
variation on the finite index `Fin M` to vanish.

* `tendsto_residual_map_sel` — `((μs n)_#sel − (μs n)_#sel ⊓ μ_#sel)(univ) → 0`.

Proof. Portmanteau (`tendsto_measure_of_null_frontier_of_tendsto'`) gives atomwise convergence
`(μs n)(sel⁻¹{i}) → μ(sel⁻¹{i})` on each continuity-set cell; `min` is continuous, so
`∑ᵢ min ((μs n)_#sel{i}) (μ_#sel{i}) → ∑ᵢ μ_#sel{i} = 1`. Squeezed between that and the constant `1`
(via the banked `sum_min_le_inf_univ`), the shared mass `((μs n)_#sel ⊓ μ_#sel)(univ) → 1`, so the
residual `1 − shared → 0`.

Combined (next leaf) with `tv_map_le` — which contracts `TV(r_#·)` for the fused rounding
`r = g ∘ sel` onto this `Fin M` residual — and `W1_le_two_mul_tv`, this drives the middle term of the
`weak ⇒ W₁` triangle to `0`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal BigOperators

namespace MeasureToMeasure

variable {d : ℕ}

/-- **Cell total variation vanishes under weak convergence.** For a measurable finite cell map
`sel : Eucl d → Fin M` whose cells are all `μ`-continuity sets, and `μs → μ` weakly, the
residual mass `((μs n)_#sel − (μs n)_#sel ⊓ μ_#sel)(univ)` — the total variation of the pushforwards
on `Fin M` — tends to `0`. -/
theorem tendsto_residual_map_sel
    {μs : ℕ → ProbabilityMeasure (Eucl d)} {μ : ProbabilityMeasure (Eucl d)}
    {M : ℕ} {sel : Eucl d → Fin M} (hsel : Measurable sel)
    (hfront : ∀ i, (μ : Measure (Eucl d)) (frontier (sel ⁻¹' {i})) = 0)
    (hconv : Tendsto μs atTop (𝓝 μ)) :
    Tendsto (fun n => (((μs n : Measure (Eucl d)).map sel)
        - ((μs n : Measure (Eucl d)).map sel) ⊓ ((μ : Measure (Eucl d)).map sel)) Set.univ)
      atTop (𝓝 0) := by
  classical
  set Q : Measure (Fin M) := (μ : Measure (Eucl d)).map sel with hQ
  haveI hQprob : IsProbabilityMeasure Q :=
    Measure.isProbabilityMeasure_map (μ := (μ : Measure (Eucl d))) hsel.aemeasurable
  have hPprob : ∀ n, IsProbabilityMeasure ((μs n : Measure (Eucl d)).map sel) :=
    fun n => Measure.isProbabilityMeasure_map (μ := (μs n : Measure (Eucl d))) hsel.aemeasurable
  -- Atomwise cell-mass convergence (portmanteau on the continuity-set cells).
  have hatom : ∀ i, Tendsto (fun n => ((μs n : Measure (Eucl d)).map sel) {i}) atTop (𝓝 (Q {i})) := by
    intro i
    have hport := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hconv (hfront i)
    simp only [← Measure.map_apply hsel (measurableSet_singleton i)] at hport
    exact hport
  -- The pointwise-minimum sum converges to the total mass 1.
  have hsum : Tendsto
      (fun n => ∑ i, min (((μs n : Measure (Eucl d)).map sel) {i}) (Q {i})) atTop (𝓝 1) := by
    have h1 : Tendsto
        (fun n => ∑ i, min (((μs n : Measure (Eucl d)).map sel) {i}) (Q {i})) atTop
        (𝓝 (∑ i, Q {i})) := by
      refine tendsto_finsetSum _ (fun i _ => ?_)
      have := (hatom i).min (tendsto_const_nhds (x := Q {i}))
      simpa using this
    have h2 : (∑ i, Q {i}) = 1 := by
      rw [sum_measure_singleton, Finset.coe_univ, measure_univ]
    rwa [h2] at h1
  -- The shared mass is squeezed up to 1 between the min-sum and the constant total mass 1.
  have hinf : Tendsto
      (fun n => (((μs n : Measure (Eucl d)).map sel) ⊓ Q) Set.univ) atTop (𝓝 1) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hsum tendsto_const_nhds
      (fun n => sum_min_le_inf_univ _ _) (fun n => ?_)
    haveI := hPprob n
    calc (((μs n : Measure (Eucl d)).map sel) ⊓ Q) Set.univ
        ≤ ((μs n : Measure (Eucl d)).map sel) Set.univ := Measure.le_iff'.1 inf_le_left Set.univ
      _ = 1 := measure_univ
  -- Residual mass = 1 − shared mass, which tends to 1 − 1 = 0.
  have hres : ∀ n,
      (((μs n : Measure (Eucl d)).map sel) - ((μs n : Measure (Eucl d)).map sel) ⊓ Q) Set.univ
        = 1 - (((μs n : Measure (Eucl d)).map sel) ⊓ Q) Set.univ := by
    intro n
    haveI := hPprob n
    haveI : IsFiniteMeasure (((μs n : Measure (Eucl d)).map sel) ⊓ Q) :=
      isFiniteMeasure_of_le _ inf_le_left
    rw [Measure.sub_apply MeasurableSet.univ inf_le_left, measure_univ]
  simp_rw [hres]
  have hfin := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ℝ≥0∞))) hinf (Or.inl ENNReal.one_ne_top)
  rwa [tsub_self] at hfin

end MeasureToMeasure
