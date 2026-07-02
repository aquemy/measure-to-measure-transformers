import MeasureToMeasure.Foundations.Sphere

/-!
# Optimal transport: couplings and the `W₁` Kantorovich cost

Mathlib `v4.31.0` has the Lévy-Prokhorov metric (the topology of weak convergence) but **no**
optimal-transport theory: no couplings, no Wasserstein distances, no Kantorovich duality
(`Axioms/Wasserstein.lean` axiomatizes `W1`/`W2`). This file begins building the real theory (M2),
starting with the two objects everything else rests on: a **coupling** of two measures, and the
**`W₁` Kantorovich transport cost** as the infimum of `∫ dist` over couplings.

We work with the `ℝ≥0∞`-valued cost (`edist`, a total lintegral), which makes the lattice structure
clean: the infimum is always defined, nonnegativity is free, and the basic metric facts
(`W₁ μ μ = 0`, symmetry) are unconditional. This is the substrate on which the Kantorovich-Rubinstein
bound and the triangle inequality (the harder, gluing-based facts) will be built.
-/

namespace MeasureToMeasure

open MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- A **coupling** (transport plan) of two measures `μ, ν` on `ℝ^d`: a measure `π` on the product
whose marginals are `μ` and `ν`. The feasible set of the Kantorovich problem. -/
def IsCoupling (π : Measure (Eucl d × Eucl d)) (μ ν : Measure (Eucl d)) : Prop :=
  π.fst = μ ∧ π.snd = ν

/-- The **product coupling** `μ ⊗ ν` is a coupling (the "independent" transport plan). Requires both
factors to be probability measures so the marginals come out exactly `μ` and `ν`. -/
theorem isCoupling_prod (μ ν : Measure (Eucl d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsCoupling (μ.prod ν) μ ν :=
  ⟨Measure.fst_prod, Measure.snd_prod⟩

/-- The **diagonal coupling** `(id, id)_# μ` couples `μ` with itself: all mass sits on the diagonal
`{(x, x)}`. This is the zero-cost plan witnessing `W₁ μ μ = 0`. -/
theorem isCoupling_diagonal (μ : Measure (Eucl d)) :
    IsCoupling (μ.map (fun x => (x, x))) μ μ := by
  have hm : Measurable (fun x : Eucl d => (x, x)) := by fun_prop
  have hfst : (Prod.fst ∘ fun x : Eucl d => (x, x)) = id := rfl
  have hsnd : (Prod.snd ∘ fun x : Eucl d => (x, x)) = id := rfl
  refine ⟨?_, ?_⟩
  · show (μ.map (fun x => (x, x))).map Prod.fst = μ
    rw [Measure.map_map measurable_fst hm, hfst, Measure.map_id]
  · show (μ.map (fun x => (x, x))).map Prod.snd = μ
    rw [Measure.map_map measurable_snd hm, hsnd, Measure.map_id]

/-- Swapping the two coordinates of a coupling of `μ, ν` gives a coupling of `ν, μ`: the marginals
exchange (`Measure.fst_map_swap` / `snd_map_swap`). The symmetry `W₁ μ ν = W₁ ν μ` descends from this. -/
theorem IsCoupling.swap {π : Measure (Eucl d × Eucl d)} {μ ν : Measure (Eucl d)}
    (h : IsCoupling π μ ν) : IsCoupling (π.map Prod.swap) ν μ := by
  refine ⟨?_, ?_⟩
  · rw [Measure.fst_map_swap]; exact h.2
  · rw [Measure.snd_map_swap]; exact h.1

/-- The **transport cost** of a plan `π`: the total expected distance `∫ dist(x, y) dπ(x, y)`,
computed as an extended-nonnegative lower integral of `edist`. -/
noncomputable def transportCost (π : Measure (Eucl d × Eucl d)) : ℝ≥0∞ :=
  ∫⁻ p, edist p.1 p.2 ∂π

/-- The transport cost is invariant under swapping coordinates (distance is symmetric). -/
theorem transportCost_swap (π : Measure (Eucl d × Eucl d)) :
    transportCost (π.map Prod.swap) = transportCost π := by
  rw [transportCost, lintegral_map (by fun_prop) measurable_swap]
  simp only [Prod.fst_swap, Prod.snd_swap, transportCost]
  exact lintegral_congr fun p => edist_comm p.2 p.1

/-- The diagonal coupling has zero transport cost (`edist x x = 0`). -/
theorem transportCost_diagonal (μ : Measure (Eucl d)) :
    transportCost (μ.map (fun x => (x, x))) = 0 := by
  rw [transportCost, lintegral_map (by fun_prop) (by fun_prop)]
  simp

/-- The **`W₁` Kantorovich transport cost** between `μ` and `ν`: the infimum of the transport cost
over all couplings. The `ℝ≥0∞`-valued Wasserstein-1 "distance"; the metric axioms are proved below
(symmetry, `W₁ μ μ = 0`) or deferred (triangle inequality needs gluing). -/
noncomputable def W1 (μ ν : Measure (Eucl d)) : ℝ≥0∞ :=
  ⨅ (π : Measure (Eucl d × Eucl d)) (_ : IsCoupling π μ ν), transportCost π

/-- Every coupling upper-bounds `W₁`: `W₁ μ ν ≤ transportCost π` for any plan `π` of `μ, ν`. -/
theorem W1_le_transportCost {π : Measure (Eucl d × Eucl d)} {μ ν : Measure (Eucl d)}
    (h : IsCoupling π μ ν) : W1 μ ν ≤ transportCost π :=
  iInf_le_of_le π (iInf_le_of_le h le_rfl)

/-- `W₁` vanishes on the diagonal: `W₁ μ μ = 0`, witnessed by the zero-cost diagonal coupling. -/
theorem W1_self_eq_zero (μ : Measure (Eucl d)) : W1 μ μ = 0 := by
  refine le_antisymm ?_ bot_le
  calc W1 μ μ ≤ transportCost (μ.map (fun x => (x, x))) :=
        W1_le_transportCost (isCoupling_diagonal μ)
    _ = 0 := transportCost_diagonal μ

/-- **Symmetry** of `W₁`: `W₁ μ ν = W₁ ν μ`. Each coupling of one pair swaps to a coupling of the
other with equal cost, so the two infima coincide. -/
theorem W1_comm (μ ν : Measure (Eucl d)) : W1 μ ν = W1 ν μ := by
  suffices h : ∀ α β : Measure (Eucl d), W1 α β ≤ W1 β α from le_antisymm (h μ ν) (h ν μ)
  intro α β
  refine le_iInf₂ fun π hπ => ?_
  calc W1 α β ≤ transportCost (π.map Prod.swap) := W1_le_transportCost hπ.swap
    _ = transportCost π := transportCost_swap π

/-!
## The Kantorovich-Rubinstein bound (one direction)

For a `1`-Lipschitz test function `f`, the dual pairing `∫ f dμ - ∫ f dν` lower-bounds the transport
cost of *every* coupling, hence lower-bounds `W₁`. This is the direction of Kantorovich-Rubinstein
duality the paper uses (the Markov bound, Claim 2). The mechanism: push `f` through both marginals of
a coupling `π`, so the pairing becomes `∫ (f p.1 - f p.2) dπ`, then bound the integrand by
`dist p.1 p.2` (Lipschitz) and integrate.
-/

/-- **Kantorovich-Rubinstein, per coupling.** For a `1`-Lipschitz `f` and a coupling `π` of `μ, ν`
with finite transport cost, the dual pairing is bounded by the plan's average distance:
`∫ f dμ - ∫ f dν ≤ ∫ dist(x, y) dπ`. -/
theorem lipschitz_integral_sub_le_transportCost {f : Eucl d → ℝ} (hf : LipschitzWith 1 f)
    {π : Measure (Eucl d × Eucl d)} {μ ν : Measure (Eucl d)} (hπ : IsCoupling π μ ν)
    (hfμ : Integrable f μ) (hfν : Integrable f ν)
    (hcost : Integrable (fun p => dist p.1 p.2) π) :
    ∫ x, f x ∂μ - ∫ x, f x ∂ν ≤ ∫ p, dist p.1 p.2 ∂π := by
  obtain ⟨hfst, hsnd⟩ := hπ
  have hfst' : π.map Prod.fst = μ := hfst
  have hsnd' : π.map Prod.snd = ν := hsnd
  have haem1 : AEStronglyMeasurable f (π.map Prod.fst) := by
    rw [hfst']; exact hfμ.aestronglyMeasurable
  have haem2 : AEStronglyMeasurable f (π.map Prod.snd) := by
    rw [hsnd']; exact hfν.aestronglyMeasurable
  -- Rewrite each marginal integral as an integral over the coupling.
  have hμ : ∫ x, f x ∂μ = ∫ p, f p.1 ∂π := by
    rw [← hfst']; exact integral_map measurable_fst.aemeasurable haem1
  have hν : ∫ x, f x ∂ν = ∫ p, f p.2 ∂π := by
    rw [← hsnd']; exact integral_map measurable_snd.aemeasurable haem2
  -- Integrability of the two pushed-forward test functions against `π`.
  have hf1 : Integrable (fun p => f p.1) π :=
    (integrable_map_measure haem1 measurable_fst.aemeasurable).mp (by rw [hfst']; exact hfμ)
  have hf2 : Integrable (fun p => f p.2) π :=
    (integrable_map_measure haem2 measurable_snd.aemeasurable).mp (by rw [hsnd']; exact hfν)
  rw [hμ, hν, ← integral_sub hf1 hf2]
  refine integral_mono (hf1.sub hf2) hcost (fun p => ?_)
  -- Pointwise: `f p.1 - f p.2 ≤ |f p.1 - f p.2| = dist (f p.1) (f p.2) ≤ dist p.1 p.2`.
  have hlip : dist (f p.1) (f p.2) ≤ dist p.1 p.2 := by
    simpa using hf.dist_le_mul p.1 p.2
  calc f p.1 - f p.2 ≤ |f p.1 - f p.2| := le_abs_self _
    _ = dist (f p.1) (f p.2) := (Real.dist_eq _ _).symm
    _ ≤ dist p.1 p.2 := hlip

/-- **Kantorovich-Rubinstein lower bound for `W₁`.** For an integrable `1`-Lipschitz `f`, the dual
pairing lower-bounds `W₁`: `ENNReal.ofReal (∫ f dμ - ∫ f dν) ≤ W₁ μ ν`. This is the direction of
Kantorovich-Rubinstein duality the paper's Markov bound (Claim 2) uses; discharging the axiom
`W1_ge_of_lipschitz` reduces to this once the ℝ≥0∞/ℝ bookkeeping is threaded at the use sites. -/
theorem ofReal_integral_sub_le_W1 {f : Eucl d → ℝ} (hf : LipschitzWith 1 f)
    {μ ν : Measure (Eucl d)} (hfμ : Integrable f μ) (hfν : Integrable f ν) :
    ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν) ≤ W1 μ ν := by
  refine le_iInf₂ fun π hπ => ?_
  rcases eq_or_ne (transportCost π) ⊤ with hfin | hfin
  · rw [hfin]; exact le_top
  -- Finite cost: `dist` is `π`-integrable and its Bochner integral is `(transportCost π).toReal`.
  have hnonneg : 0 ≤ᵐ[π] fun p => dist p.1 p.2 := ae_of_all _ fun _ => dist_nonneg
  have haesm : AEStronglyMeasurable (fun p : Eucl d × Eucl d => dist p.1 p.2) π :=
    continuous_dist.aestronglyMeasurable
  have hlint : ∫⁻ p, ENNReal.ofReal (dist p.1 p.2) ∂π = transportCost π :=
    lintegral_congr fun p => (edist_dist p.1 p.2).symm
  have hcost : Integrable (fun p => dist p.1 p.2) π := by
    refine ⟨haesm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnonneg, hlint]
    exact lt_top_iff_ne_top.mpr hfin
  have hcost_eq : ∫ p, dist p.1 p.2 ∂π = (transportCost π).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae hnonneg haesm, hlint]
  have hbound := lipschitz_integral_sub_le_transportCost hf hπ hfμ hfν hcost
  rw [hcost_eq] at hbound
  calc ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν)
      ≤ ENNReal.ofReal (transportCost π).toReal := ENNReal.ofReal_le_ofReal hbound
    _ = transportCost π := ENNReal.ofReal_toReal hfin

end MeasureToMeasure
