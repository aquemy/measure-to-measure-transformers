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

end MeasureToMeasure
