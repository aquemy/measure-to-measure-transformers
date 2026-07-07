import MeasureToMeasure.Foundations.WeakToTV
import MeasureToMeasure.Foundations.SphereRounding
import MeasureToMeasure.Foundations.WassersteinTV
import MeasureToMeasure.Foundations.WassersteinMap

/-!
# Weak convergence implies `W₁` convergence on the sphere (M3b existence, leaf S3b-iv-glue)

The crux of the Wasserstein sub-campaign toward `exists_meanFieldFlow` (M3b existence): the hard
direction `weak ⇒ W₁` for sphere-supported probability measures. This assembles the banked pieces
into the sequential statement Prokhorov-style completeness needs.

* `tendsto_W1_of_tendsto` — if `μs → μ` weakly (`ProbabilityMeasure (Eucl d)`) and every `μs n`, `μ`
  is supported on `sphere d`, then `W1 (μs n) μ → 0`.

Proof (the cell-rounding argument). Fix a real scale `δ` (chosen below `ε`). `exists_finite_rounding`
gives a measurable finite cell map `sel : Eucl d → Fin M`, sphere representatives `g : Fin M → Eucl d`,
displacement `dist y (g (sel y)) < 2δ` on the sphere, and `μ`-null cell frontiers. Put `r = g ∘ sel`.
The `W₁` triangle splits `W1(μs n, μ)` into three:

* `W1(μs n, (μs n)_#r) ≤ 2δ` and `W1(μ_#r, μ) ≤ 2δ` — the rounding displacement bound
  (`W1_map_le_of_ae_edist_le`, sphere-supported so a.e. valid);
* `W1((μs n)_#r, μ_#r) ≤ 2·TV((μs n)_#r, μ_#r)` (`W1_le_two_mul_tv`, both pushforwards sphere-supported),
  and `TV((μs n)_#r, μ_#r) ≤ TV((μs n)_#sel, μ_#sel)` (`tv_map_le`, contracting onto the finite `Fin M`),
  which `→ 0` by `tendsto_residual_map_sel` (portmanteau on the continuity-set cells).

Hence `W1(μs n, μ) ≤ 4δ + 2·(→0)`; choosing `4δ < ε` and taking `n` large gives `W1(μs n, μ) ≤ ε`.

M3b staging: consumed when `exists_meanFieldFlow` is discharged; see RESEARCH.md.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace MeasureToMeasure

variable {d : ℕ}

/-- **Weak convergence implies `W₁` convergence for sphere-supported probability measures.** If
`μs → μ` in the weak topology of `ProbabilityMeasure (Eucl d)` and every `μs n` and `μ` is supported
on `sphere d`, then `W1 (μs n) μ → 0`. This is the hard direction of the `W₁`/weak metrization on the
compact sphere (Mathlib has no optimal transport); it is built from the elementary cell-rounding
coupling rather than Kantorovich–Rubinstein duality. -/
theorem tendsto_W1_of_tendsto
    {μs : ℕ → ProbabilityMeasure (Eucl d)} {μ : ProbabilityMeasure (Eucl d)}
    (hμs : ∀ n, (μs n : Measure (Eucl d)) (sphere d)ᶜ = 0)
    (hμ : (μ : Measure (Eucl d)) (sphere d)ᶜ = 0)
    (hconv : Tendsto μs atTop (𝓝 μ)) :
    Tendsto (fun n => W1 (μs n : Measure (Eucl d)) (μ : Measure (Eucl d))) atTop (𝓝 0) := by
  classical
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  -- Pick a real rounding scale `δ` whose full offset `4δ` sits strictly below `ε`.
  obtain ⟨c, hc0, hcε⟩ := exists_between hε
  have hc_top : c ≠ ⊤ := (hcε.trans_le le_top).ne
  set δ : ℝ := c.toReal / 4 with hδdef
  have hδ0 : 0 < δ := by
    have hct : 0 < c.toReal := ENNReal.toReal_pos hc0.ne' hc_top
    rw [hδdef]; positivity
  have hofReal4δ : ENNReal.ofReal (4 * δ) = c := by
    rw [hδdef, show (4 : ℝ) * (c.toReal / 4) = c.toReal from by ring, ENNReal.ofReal_toReal hc_top]
  -- The rounding data at scale `δ`, built against the limit `μ`.
  obtain ⟨M, sel, g, hsel, hg_sphere, hdisp, hfront⟩ :=
    exists_finite_rounding (μ : Measure (Eucl d)) hμ hδ0
  have hg_meas : Measurable g := measurable_from_top
  set r : Eucl d → Eucl d := fun y => g (sel y) with hrdef
  have hr_meas : Measurable r := hg_meas.comp hsel
  have hr_sphere : ∀ y, r y ∈ sphere d := fun y => hg_sphere (sel y)
  -- Pushforward by `r` lands on the sphere, so `ν_#r` is sphere-supported for any `ν`.
  have hpre : r ⁻¹' (sphere d)ᶜ = ∅ := by
    ext y; simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
    exact hr_sphere y
  have hmscompl : MeasurableSet ((sphere d)ᶜ) := Metric.isClosed_sphere.measurableSet.compl
  have hmap_sphere : ∀ ν : Measure (Eucl d), (ν.map r) (sphere d)ᶜ = 0 := fun ν => by
    rw [Measure.map_apply hr_meas hmscompl, hpre, measure_empty]
  -- `ν_#r = (ν_#sel)_#g`, the factorisation used to contract the total variation onto `Fin M`.
  have hmapmap : ∀ ν : Measure (Eucl d), ν.map r = (ν.map sel).map g := fun ν =>
    (Measure.map_map hg_meas hsel).symm
  -- The finite-index residual (its vanishing is the portmanteau leaf).
  set residualFn : ℕ → ℝ≥0∞ :=
    (fun n => (((μs n : Measure (Eucl d)).map sel)
      - ((μs n : Measure (Eucl d)).map sel) ⊓ ((μ : Measure (Eucl d)).map sel)) Set.univ)
    with hresF
  have htv : Tendsto residualFn atTop (𝓝 0) := tendsto_residual_map_sel hsel hfront hconv
  -- a.e. displacement bound for a sphere-supported measure.
  have hAe : ∀ ν : Measure (Eucl d), ν (sphere d)ᶜ = 0 →
      (∀ᵐ y ∂ν, edist y (r y) ≤ ENNReal.ofReal (2 * δ)) := by
    intro ν hν
    have hsph : ∀ᵐ y ∂ν, y ∈ sphere d := by rw [ae_iff]; exact hν
    filter_upwards [hsph] with y hy
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (hdisp y hy).le
  -- The per-`n` triangle bound: `W1(μs n, μ) ≤ 4δ + 2·residual n`.
  have hbound : ∀ n, W1 (μs n : Measure (Eucl d)) (μ : Measure (Eucl d))
      ≤ ENNReal.ofReal (4 * δ) + 2 * residualFn n := by
    intro n
    haveI hPr : IsProbabilityMeasure ((μs n : Measure (Eucl d)).map r) :=
      Measure.isProbabilityMeasure_map (μ := (μs n : Measure (Eucl d))) hr_meas.aemeasurable
    haveI hQr : IsProbabilityMeasure ((μ : Measure (Eucl d)).map r) :=
      Measure.isProbabilityMeasure_map (μ := (μ : Measure (Eucl d))) hr_meas.aemeasurable
    have hA : W1 (μs n : Measure (Eucl d)) ((μs n : Measure (Eucl d)).map r)
        ≤ ENNReal.ofReal (2 * δ) := W1_map_le_of_ae_edist_le hr_meas (hAe _ (hμs n))
    have hC : W1 ((μ : Measure (Eucl d)).map r) (μ : Measure (Eucl d)) ≤ ENNReal.ofReal (2 * δ) := by
      rw [W1_comm]; exact W1_map_le_of_ae_edist_le hr_meas (hAe _ hμ)
    have hBtv : W1 ((μs n : Measure (Eucl d)).map r) ((μ : Measure (Eucl d)).map r)
        ≤ 2 * ((((μs n : Measure (Eucl d)).map r)
          - ((μs n : Measure (Eucl d)).map r) ⊓ ((μ : Measure (Eucl d)).map r)) Set.univ) :=
      W1_le_two_mul_tv (hmap_sphere _) (hmap_sphere _)
    have hTVcontract : ((((μs n : Measure (Eucl d)).map r)
        - ((μs n : Measure (Eucl d)).map r) ⊓ ((μ : Measure (Eucl d)).map r)) Set.univ)
        ≤ residualFn n := by
      haveI : IsProbabilityMeasure ((μs n : Measure (Eucl d)).map sel) :=
        Measure.isProbabilityMeasure_map (μ := (μs n : Measure (Eucl d))) hsel.aemeasurable
      haveI : IsProbabilityMeasure ((μ : Measure (Eucl d)).map sel) :=
        Measure.isProbabilityMeasure_map (μ := (μ : Measure (Eucl d))) hsel.aemeasurable
      rw [hresF, hmapmap (μs n : Measure (Eucl d)), hmapmap (μ : Measure (Eucl d))]
      exact tv_map_le hg_meas ((μs n : Measure (Eucl d)).map sel) ((μ : Measure (Eucl d)).map sel)
    calc W1 (μs n : Measure (Eucl d)) (μ : Measure (Eucl d))
        ≤ W1 (μs n : Measure (Eucl d)) ((μs n : Measure (Eucl d)).map r)
          + W1 ((μs n : Measure (Eucl d)).map r) (μ : Measure (Eucl d)) := W1_triangle _ _ _
      _ ≤ W1 (μs n : Measure (Eucl d)) ((μs n : Measure (Eucl d)).map r)
          + (W1 ((μs n : Measure (Eucl d)).map r) ((μ : Measure (Eucl d)).map r)
            + W1 ((μ : Measure (Eucl d)).map r) (μ : Measure (Eucl d))) := by
          gcongr; exact W1_triangle _ _ _
      _ ≤ ENNReal.ofReal (2 * δ)
          + (2 * ((((μs n : Measure (Eucl d)).map r)
              - ((μs n : Measure (Eucl d)).map r) ⊓ ((μ : Measure (Eucl d)).map r)) Set.univ)
            + ENNReal.ofReal (2 * δ)) := add_le_add hA (add_le_add hBtv hC)
      _ ≤ ENNReal.ofReal (2 * δ) + (2 * residualFn n + ENNReal.ofReal (2 * δ)) := by
          gcongr
      _ = ENNReal.ofReal (4 * δ) + 2 * residualFn n := by
          rw [add_comm (2 * residualFn n) (ENNReal.ofReal (2 * δ)), ← add_assoc,
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            show (2 : ℝ) * δ + 2 * δ = 4 * δ from by ring]
  -- Take `n` large: the residual is eventually below the slack `ε - c`.
  have hgap : 0 < ε - c := tsub_pos_of_lt hcε
  have h2res : Tendsto (fun n => 2 * residualFn n) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞)) htv (Or.inr (by norm_num))
    simpa using h
  filter_upwards [h2res.eventually (Iio_mem_nhds hgap)] with n hn
  refine le_of_lt ?_
  calc W1 (μs n : Measure (Eucl d)) (μ : Measure (Eucl d))
      ≤ ENNReal.ofReal (4 * δ) + 2 * residualFn n := hbound n
    _ = c + 2 * residualFn n := by rw [hofReal4δ]
    _ < c + (ε - c) := ENNReal.add_lt_add_left hc_top hn
    _ = ε := add_tsub_cancel_of_le hcε.le

end MeasureToMeasure
