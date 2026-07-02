import MeasureToMeasure.Axioms.Wasserstein

/-!
# Leaf L8: the Markov-type mass bound (Claim 2)

Claim 2 (Appendix B.5, p.39) states: if `W₂(μ, δ_{x₀}) ≤ η₂` then `1 - μ(B(x₀, η₃)) ≤ C η₂ / η₃`, i.e.
a measure `W₂`-close to a Dirac puts almost all its mass near `x₀`. The proof is a Markov inequality
driven by a Lipschitz bump and Kantorovich-Rubinstein duality.

We formalize it over the `W₁` axiom (`W1_ge_of_lipschitz`, the KR-duality direction the paper uses),
so the result's status is `math.axiomatised`. What is **machine-checked here** is the whole argument
*given* that axiom: the truncated-distance bump `f(x) = min(η₃, d(x,x₀))` is `1`-Lipschitz, vanishes
at `x₀`, and dominates `η₃ · 𝟙_{d(·,x₀) ≥ η₃}`, whence
`η₃ · μ{d(·,x₀) ≥ η₃} ≤ ∫ f dμ = ∫ f dμ - f(x₀) ≤ W₁(μ, δ_{x₀}) ≤ C η₂`.
The set `{x | η₃ ≤ d(x, x₀)}` is the complement of the open ball `B(x₀, η₃)`, so for a probability
measure this is exactly `1 - μ(B(x₀, η₃)) ≤ C η₂ / η₃`.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory MeasureToMeasure.Axioms

variable {d : ℕ}

/-- The truncated-distance bump `f(x) = min(η₃, d(x, x₀))`. -/
noncomputable def distBump (x₀ : Eucl d) (η₃ : ℝ) (x : Eucl d) : ℝ := min η₃ (dist x x₀)

/-- The bump is `1`-Lipschitz (a truncation of the `1`-Lipschitz distance). Proved through the
`dist`-characterization to avoid the `EuclideanSpace`/`PiLp` extended-metric instance diamond. -/
theorem distBump_lipschitz (x₀ : Eucl d) (η₃ : ℝ) : LipschitzWith 1 (distBump x₀ η₃) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  -- `t ↦ min η₃ t` is 1-Lipschitz on ℝ (no PiLp instance diamond on the codomain)
  have hL : LipschitzWith 1 (fun t : ℝ => min η₃ t) := LipschitzWith.const_min LipschitzWith.id η₃
  have hmin := hL.dist_le_mul (dist x x₀) (dist y x₀)
  simp only [distBump, Real.dist_eq, NNReal.coe_one, one_mul] at hmin ⊢
  exact hmin.trans (abs_dist_sub_le x y x₀)

theorem distBump_nonneg {x₀ : Eucl d} {η₃ : ℝ} (hη₃ : 0 ≤ η₃) (x : Eucl d) :
    0 ≤ distBump x₀ η₃ x :=
  le_min hη₃ dist_nonneg

/-- On the complement of the ball the bump saturates at `η₃`. -/
theorem distBump_eq_outside {x₀ : Eucl d} {η₃ : ℝ} {x : Eucl d} (hx : η₃ ≤ dist x x₀) :
    distBump x₀ η₃ x = η₃ :=
  min_eq_left hx

/-- **Lemma L8 / Claim 2 (Markov bound).** For a probability measure with
`W₁(μ, δ_{x₀}) ≤ C η₂`, the mass at geodesic/Euclidean distance `≥ η₃` from `x₀` is at most
`C η₂ / η₃`. Equivalently `1 - μ(B(x₀, η₃)) ≤ C η₂ / η₃`. Rests on the `W₁` axiom (KR duality):
status `math.axiomatised`. -/
theorem markov_bound (μ : Measure (Eucl d)) [IsProbabilityMeasure μ]
    (x₀ : Eucl d) (η₂ η₃ C : ℝ) (hη₃ : 0 < η₃)
    (hfin : MeasureToMeasure.W1 μ (Measure.dirac x₀) ≠ ⊤)
    (hW1 : MeasureToMeasure.Axioms.W1 μ (Measure.dirac x₀) ≤ C * η₂) :
    μ.real {x | η₃ ≤ dist x x₀} ≤ C * η₂ / η₃ := by
  set s : Set (Eucl d) := {x | η₃ ≤ dist x x₀} with hs
  have hcont : Continuous (fun x : Eucl d => dist x x₀) := by fun_prop
  have hsmeas : MeasurableSet s := measurableSet_le measurable_const hcont.measurable
  -- the bump is integrable (bounded by η₃ on a finite measure)
  have hbump_int : Integrable (distBump x₀ η₃) μ := by
    refine Integrable.mono' (integrable_const η₃)
      (distBump_lipschitz x₀ η₃).continuous.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (distBump_nonneg hη₃.le x)]
    exact min_le_left _ _
  have hind_int : Integrable (s.indicator (fun _ => η₃)) μ :=
    (integrable_const η₃).indicator hsmeas
  -- η₃ · 𝟙_s ≤ bump pointwise
  have hdom : s.indicator (fun _ => η₃) ≤ distBump x₀ η₃ := by
    intro x
    by_cases hx : x ∈ s
    · rw [Set.indicator_apply, if_pos hx]; exact (distBump_eq_outside hx).ge
    · rw [Set.indicator_apply, if_neg hx]; exact distBump_nonneg hη₃.le x
  -- ∫ η₃·𝟙_s dμ = η₃ · μ(s)
  have hint_ind : ∫ x, s.indicator (fun _ => η₃) x ∂μ = μ.real s * η₃ := by
    rw [integral_indicator_const η₃ hsmeas, smul_eq_mul]
  -- ∫ bump dδ_{x₀} = f(x₀) = 0
  have hdirac : ∫ x, distBump x₀ η₃ x ∂(Measure.dirac x₀) = 0 := by
    rw [integral_dirac]
    simp [distBump, min_eq_right hη₃.le]
  -- the bump is integrable against the Dirac (finite measure, bounded function)
  have hbump_int_dirac : Integrable (distBump x₀ η₃) (Measure.dirac x₀) := by
    refine Integrable.mono' (integrable_const η₃)
      (distBump_lipschitz x₀ η₃).continuous.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (distBump_nonneg hη₃.le x)]
    exact min_le_left _ _
  -- KR duality (now a theorem): ∫ bump dμ - ∫ bump dδ ≤ W₁
  have hdual := W1_ge_of_lipschitz μ (Measure.dirac x₀) (distBump x₀ η₃) (distBump_lipschitz x₀ η₃)
    hbump_int hbump_int_dirac hfin
  rw [hdirac, sub_zero] at hdual
  -- assemble: η₃ · μ(s) ≤ ∫ bump dμ ≤ W₁ ≤ C η₂
  have hmono : μ.real s * η₃ ≤ ∫ x, distBump x₀ η₃ x ∂μ := by
    rw [← hint_ind]; exact integral_mono hind_int hbump_int hdom
  have key : μ.real s * η₃ ≤ C * η₂ := le_trans hmono (le_trans hdual hW1)
  rw [le_div_iff₀ hη₃]
  exact key

end MeasureToMeasure.Leaves
