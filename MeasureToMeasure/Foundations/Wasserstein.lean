import MeasureToMeasure.Foundations.Sphere
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableLIntegral

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

open MeasureTheory ProbabilityTheory
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
  -- Substitute the marginals (`π.fst` is *definitionally* `π.map Prod.fst`).
  obtain ⟨rfl, rfl⟩ := hπ
  have hμ : ∫ x, f x ∂π.fst = ∫ p, f p.1 ∂π :=
    integral_map measurable_fst.aemeasurable hfμ.aestronglyMeasurable
  have hν : ∫ x, f x ∂π.snd = ∫ p, f p.2 ∂π :=
    integral_map measurable_snd.aemeasurable hfν.aestronglyMeasurable
  -- Integrability of the two pushed-forward test functions against `π`.
  have hf1 : Integrable (fun p => f p.1) π :=
    (integrable_map_measure hfμ.aestronglyMeasurable measurable_fst.aemeasurable).mp hfμ
  have hf2 : Integrable (fun p => f p.2) π :=
    (integrable_map_measure hfν.aestronglyMeasurable measurable_snd.aemeasurable).mp hfν
  rw [hμ, hν, ← integral_sub hf1 hf2]
  -- Pointwise: `f p.1 - f p.2 ≤ dist (f p.1) (f p.2) ≤ dist p.1 p.2`.
  refine integral_mono (hf1.sub hf2) hcost fun p =>
    (Real.sub_le_dist _ _).trans (by simpa using hf.dist_le_mul p.1 p.2)

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
  calc ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν)
      ≤ ENNReal.ofReal (∫ p, dist p.1 p.2 ∂π) :=
        ENNReal.ofReal_le_ofReal (lipschitz_integral_sub_le_transportCost hf hπ hfμ hfν hcost)
    _ = ∫⁻ p, ENNReal.ofReal (dist p.1 p.2) ∂π := ofReal_integral_eq_lintegral_ofReal hcost hnonneg
    _ = transportCost π := hlint

/-!
## The triangle inequality via gluing of couplings

`W₁ μ ρ ≤ W₁ μ ν + W₁ ν ρ`. The classical proof glues a plan `π₁` of `(μ, ν)` and a plan `π₂` of
`(ν, ρ)` along their shared marginal `ν`: disintegrate `π₂ = ν ⊗ₘ κ₂` (its conditional `z | y`), lift
`κ₂` to a kernel on `X × Y` reading only the `Y`-coordinate, and form the triple
`T = π₁ ⊗ₘ (κ₂ ∘ snd)` on `(X × Y) × Z`. The `(X, Y)`-marginal of `T` is `π₁` (free from `fst_compProd`),
the `(Y, Z)`-marginal collapses to `ν ⊗ₘ κ₂ = π₂`, and the `(X, Z)`-marginal `γ` is a coupling of
`(μ, ρ)` whose cost is bounded by `cost π₁ + cost π₂` via `edist x z ≤ edist x y + edist y z`.
-/

/-- **Gluing lemma.** Given a coupling `π₁` of `(μ, ν)` and `π₂` of `(ν, ρ)`, there is a coupling `γ`
of `(μ, ρ)` with `transportCost γ ≤ transportCost π₁ + transportCost π₂`. -/
theorem exists_coupling_transportCost_le {μ ν ρ : Measure (Eucl d)} [IsProbabilityMeasure ν]
    {π₁ π₂ : Measure (Eucl d × Eucl d)} [IsProbabilityMeasure π₁] [IsProbabilityMeasure π₂]
    (h₁ : IsCoupling π₁ μ ν) (h₂ : IsCoupling π₂ ν ρ) :
    ∃ γ : Measure (Eucl d × Eucl d),
      IsCoupling γ μ ρ ∧ transportCost γ ≤ transportCost π₁ + transportCost π₂ := by
  classical
  -- Disintegrate `π₂ = ν ⊗ₘ κ₂` and lift `κ₂` to a `Y`-reading kernel on `X × Y`.
  set κ₂ : Kernel (Eucl d) (Eucl d) := π₂.condKernel with hκ₂
  have hπ₂ : ν ⊗ₘ κ₂ = π₂ := by rw [hκ₂, ← h₂.1]; exact π₂.disintegrate π₂.condKernel
  set κ : Kernel (Eucl d × Eucl d) (Eucl d) := κ₂.comap Prod.snd measurable_snd with hκ
  set T : Measure ((Eucl d × Eucl d) × Eucl d) := π₁ ⊗ₘ κ with hT
  -- The two coordinate projections used to read marginals off the triple `T`.
  have hg₁ : Measurable (fun q : (Eucl d × Eucl d) × Eucl d => (q.1.1, q.2)) := by fun_prop
  have hg₂ : Measurable (fun q : (Eucl d × Eucl d) × Eucl d => (q.1.2, q.2)) := by fun_prop
  set γ : Measure (Eucl d × Eucl d) := T.map (fun q => (q.1.1, q.2)) with hγ
  have hTfst : T.fst = π₁ := by rw [hT]; exact Measure.fst_compProd π₁ κ
  -- Crux: the `(Y, Z)`-marginal of `T` is `π₂`.
  have hm : T.map (fun q => (q.1.2, q.2)) = π₂ := by
    rw [← hπ₂]
    refine Measure.ext_of_lintegral _ fun F hF => ?_
    have hFg₂ : Measurable fun q : (Eucl d × Eucl d) × Eucl d => F (q.1.2, q.2) := hF.comp hg₂
    have hΦ : Measurable fun y => ∫⁻ z, F (y, z) ∂κ₂ y :=
      Measurable.lintegral_kernel_prod_right (κ := κ₂) (f := fun y z => F (y, z)) hF
    rw [lintegral_map hF hg₂, hT,
      Measure.lintegral_compProd hFg₂, Measure.lintegral_compProd hF]
    simp only [hκ, Kernel.comap_apply]
    rw [← h₁.2, show (π₁.snd : Measure (Eucl d)) = π₁.map Prod.snd from rfl,
      lintegral_map hΦ measurable_snd]
  refine ⟨γ, ⟨?_, ?_⟩, ?_⟩
  · -- `γ.fst = μ` (both sides are the double-`fst` marginal of `T`, by `map_map` twice)
    show γ.map Prod.fst = μ
    rw [hγ, Measure.map_map measurable_fst hg₁, ← h₁.1, ← hTfst]
    exact (Measure.map_map measurable_fst measurable_fst).symm
  · -- `γ.snd = ρ` (both sides are the last-coordinate marginal of `T`)
    show γ.map Prod.snd = ρ
    rw [hγ, Measure.map_map measurable_snd hg₁, ← h₂.2, ← hm]
    exact (Measure.map_map measurable_snd hg₂).symm
  · -- cost bound
    have hγcost : transportCost γ = ∫⁻ q, edist q.1.1 q.2 ∂T := by
      rw [transportCost, hγ, lintegral_map (by fun_prop) hg₁]
    have hT1 : ∫⁻ q, edist q.1.1 q.1.2 ∂T = transportCost π₁ := by
      rw [transportCost, ← hTfst, show (T.fst : Measure (Eucl d × Eucl d)) = T.map Prod.fst from rfl,
        lintegral_map (by fun_prop) measurable_fst]
    have hT2 : ∫⁻ q, edist q.1.2 q.2 ∂T = transportCost π₂ := by
      rw [transportCost, ← hm, lintegral_map (by fun_prop) hg₂]
    rw [hγcost, ← hT1, ← hT2,
      ← lintegral_add_left (f := fun q : (Eucl d × Eucl d) × Eucl d => edist q.1.1 q.1.2)
        (by fun_prop)]
    exact lintegral_mono fun q => edist_triangle _ _ _

/-- **Sub-additivity of `W₁` along a gluing** (probability measures): `W₁ μ ρ` is bounded by the sum
of the costs of any plan of `(μ, ν)` and any plan of `(ν, ρ)`. The per-coupling triangle inequality,
immediate from the gluing lemma. -/
theorem W1_le_transportCost_add {μ ν ρ : Measure (Eucl d)} [IsProbabilityMeasure ν]
    {π₁ π₂ : Measure (Eucl d × Eucl d)} [IsProbabilityMeasure π₁] [IsProbabilityMeasure π₂]
    (h₁ : IsCoupling π₁ μ ν) (h₂ : IsCoupling π₂ ν ρ) :
    W1 μ ρ ≤ transportCost π₁ + transportCost π₂ := by
  obtain ⟨γ, hγc, hγle⟩ := exists_coupling_transportCost_le h₁ h₂
  exact (W1_le_transportCost hγc).trans hγle

/-- **Triangle inequality for `W₁`** (probability measures): `W₁ μ ρ ≤ W₁ μ ν + W₁ ν ρ`. Descends from
the per-coupling gluing bound by distributing `+` through the two infima (`ENNReal.iInf_add` /
`add_iInf`, valid unconditionally on `ℝ≥0∞`). With `W1_self_eq_zero` and `W1_comm`, this makes `W₁` a
pseudometric on probability measures. -/
theorem W1_triangle (μ ν ρ : Measure (Eucl d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ] : W1 μ ρ ≤ W1 μ ν + W1 ν ρ := by
  have key : ∀ π₁ : Measure (Eucl d × Eucl d), IsCoupling π₁ μ ν →
      ∀ π₂ : Measure (Eucl d × Eucl d), IsCoupling π₂ ν ρ →
      W1 μ ρ ≤ transportCost π₁ + transportCost π₂ := by
    intro π₁ h₁ π₂ h₂
    have hp₁ : IsProbabilityMeasure π₁ := ⟨by rw [← Measure.fst_univ, h₁.1]; exact measure_univ⟩
    have hp₂ : IsProbabilityMeasure π₂ := ⟨by rw [← Measure.fst_univ, h₂.1]; exact measure_univ⟩
    exact W1_le_transportCost_add h₁ h₂
  have hrw : W1 μ ν + W1 ν ρ = ⨅ π₂, ⨅ (_ : IsCoupling π₂ ν ρ), ⨅ π₁, ⨅ (_ : IsCoupling π₁ μ ν),
      (transportCost π₁ + transportCost π₂) := by
    simp only [W1, ENNReal.iInf_add, ENNReal.add_iInf]
  rw [hrw]
  exact le_iInf₂ fun π₂ h₂ => le_iInf₂ fun π₁ h₁ => key π₁ h₁ π₂ h₂

/-!
## The quadratic Wasserstein cost `W₂²`

The paper's Lemma 5.2 controls `W₂` between two pushforwards of a measure by the `L²` distance of the
maps. We build the quadratic cost in squared form `W₂²` (the infimum of `∫ dist² dπ` over couplings),
staying in `ℝ≥0∞` as for `W₁`, and prove the map-coupling bound witnessed by `(T₁, T₂)_# μ`, together
with the unconditional metric facts. Taking square roots to recover `W₂` itself, and the `W₂` triangle
inequality (Minkowski/gluing), are deferred.
-/

/-- The **squared transport cost** of a plan `π`: `∫ dist(x, y)² dπ(x, y)` as an `ℝ≥0∞` lower integral. -/
noncomputable def sqTransportCost (π : Measure (Eucl d × Eucl d)) : ℝ≥0∞ :=
  ∫⁻ p, edist p.1 p.2 ^ 2 ∂π

/-- The **squared `W₂` Kantorovich cost** between `μ` and `ν`: the infimum of the squared transport
cost over all couplings. Its square root is the Wasserstein-2 distance. -/
noncomputable def W2sq (μ ν : Measure (Eucl d)) : ℝ≥0∞ :=
  ⨅ (π : Measure (Eucl d × Eucl d)) (_ : IsCoupling π μ ν), sqTransportCost π

/-- Every coupling upper-bounds `W₂²`. -/
theorem W2sq_le_sqTransportCost {π : Measure (Eucl d × Eucl d)} {μ ν : Measure (Eucl d)}
    (h : IsCoupling π μ ν) : W2sq μ ν ≤ sqTransportCost π :=
  iInf_le_of_le π (iInf_le_of_le h le_rfl)

/-- The squared transport cost is invariant under swapping coordinates. -/
theorem sqTransportCost_swap (π : Measure (Eucl d × Eucl d)) :
    sqTransportCost (π.map Prod.swap) = sqTransportCost π := by
  rw [sqTransportCost, lintegral_map (by fun_prop) measurable_swap]
  simp only [Prod.fst_swap, Prod.snd_swap, sqTransportCost]
  exact lintegral_congr fun p => by rw [edist_comm]

/-- The diagonal coupling has zero squared cost. -/
theorem sqTransportCost_diagonal (μ : Measure (Eucl d)) :
    sqTransportCost (μ.map (fun x => (x, x))) = 0 := by
  rw [sqTransportCost, lintegral_map (by fun_prop) (by fun_prop)]; simp

/-- `W₂²` vanishes on the diagonal: `W₂²(μ, μ) = 0`. -/
theorem W2sq_self_eq_zero (μ : Measure (Eucl d)) : W2sq μ μ = 0 := by
  refine le_antisymm ?_ bot_le
  calc W2sq μ μ ≤ sqTransportCost (μ.map (fun x => (x, x))) :=
        W2sq_le_sqTransportCost (isCoupling_diagonal μ)
    _ = 0 := sqTransportCost_diagonal μ

/-- **Symmetry** of `W₂²`. -/
theorem W2sq_comm (μ ν : Measure (Eucl d)) : W2sq μ ν = W2sq ν μ := by
  suffices h : ∀ α β : Measure (Eucl d), W2sq α β ≤ W2sq β α from le_antisymm (h μ ν) (h ν μ)
  intro α β
  refine le_iInf₂ fun π hπ => ?_
  calc W2sq α β ≤ sqTransportCost (π.map Prod.swap) := W2sq_le_sqTransportCost hπ.swap
    _ = sqTransportCost π := sqTransportCost_swap π

/-- **Map-coupling bound (Lemma 5.2, squared form).** The squared `W₂` distance between two
pushforwards of `μ` is at most the `L²(μ)` cost of moving `T₁` to `T₂`, witnessed by the coupling
`(T₁, T₂)_# μ`: `W₂²(T₁_# μ, T₂_# μ) ≤ ∫ dist(T₁ x, T₂ x)² dμ`. -/
theorem W2sq_map_le {μ : Measure (Eucl d)} {T₁ T₂ : Eucl d → Eucl d}
    (hT₁ : Measurable T₁) (hT₂ : Measurable T₂) :
    W2sq (μ.map T₁) (μ.map T₂) ≤ ∫⁻ x, edist (T₁ x) (T₂ x) ^ 2 ∂μ := by
  have hcpl : IsCoupling (μ.map fun x => (T₁ x, T₂ x)) (μ.map T₁) (μ.map T₂) :=
    ⟨Measure.fst_map_prodMk hT₂, Measure.snd_map_prodMk hT₁⟩
  calc W2sq (μ.map T₁) (μ.map T₂)
      ≤ sqTransportCost (μ.map fun x => (T₁ x, T₂ x)) := W2sq_le_sqTransportCost hcpl
    _ = ∫⁻ x, edist (T₁ x) (T₂ x) ^ 2 ∂μ := by
        rw [sqTransportCost, lintegral_map (by fun_prop) (by fun_prop)]

/-!
## The `W₂` transport distance and its triangle inequality (Minkowski + gluing)

`W₂ μ ν` is the infimum over couplings of the **root** cost `(∫ dist² dπ)^{1/2}`. Defining it as the
infimum of root costs (rather than `√` of `W₂²`) lets the triangle inequality descend through the two
infima exactly as for `W₁`. The per-coupling bound is Minkowski's inequality for `L²` applied to a
glued triple: `‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖` pointwise, then `ENNReal.lintegral_Lp_add_le` (`p = 2`).
-/

/-- The **`W₂` (root) Wasserstein distance**: `⨅` over couplings of `(∫ dist(x,y)² dπ)^{1/2}`. -/
noncomputable def W2 (μ ν : Measure (Eucl d)) : ℝ≥0∞ :=
  ⨅ (π : Measure (Eucl d × Eucl d)) (_ : IsCoupling π μ ν), sqTransportCost π ^ (2⁻¹ : ℝ)

/-- Every coupling upper-bounds `W₂`: `W₂ μ ν ≤ (sqTransportCost π)^{1/2}` for any plan `π`. -/
theorem W2_le_rpow_sqTransportCost {π : Measure (Eucl d × Eucl d)} {μ ν : Measure (Eucl d)}
    (h : IsCoupling π μ ν) : W2 μ ν ≤ sqTransportCost π ^ (2⁻¹ : ℝ) :=
  iInf_le_of_le π (iInf_le_of_le h le_rfl)

/-- `W₂` vanishes on the diagonal: `W₂ μ μ = 0`, via the zero-cost diagonal coupling. -/
theorem W2_self_eq_zero (μ : Measure (Eucl d)) : W2 μ μ = 0 := by
  refine le_antisymm ?_ bot_le
  calc W2 μ μ ≤ sqTransportCost (μ.map (fun x => (x, x))) ^ (2⁻¹ : ℝ) :=
        W2_le_rpow_sqTransportCost (isCoupling_diagonal μ)
    _ = 0 := by rw [sqTransportCost_diagonal μ, ENNReal.zero_rpow_of_pos (by norm_num)]

/-- **Symmetry** of `W₂`: `W₂ μ ν = W₂ ν μ`. -/
theorem W2_comm (μ ν : Measure (Eucl d)) : W2 μ ν = W2 ν μ := by
  suffices h : ∀ α β : Measure (Eucl d), W2 α β ≤ W2 β α from le_antisymm (h μ ν) (h ν μ)
  intro α β
  refine le_iInf₂ fun π hπ => ?_
  calc W2 α β ≤ sqTransportCost (π.map Prod.swap) ^ (2⁻¹ : ℝ) :=
        W2_le_rpow_sqTransportCost hπ.swap
    _ = sqTransportCost π ^ (2⁻¹ : ℝ) := by rw [sqTransportCost_swap π]

/-- **Quadratic gluing (Minkowski), per coupling.** Given a coupling `π₁` of `(μ, ν)` and `π₂` of
`(ν, ρ)`, there is a coupling `γ` of `(μ, ρ)` whose root cost is bounded by the sum of the root costs
of `π₁` and `π₂`. Reuses the gluing triple `T` and applies `L²` Minkowski. -/
theorem exists_coupling_rpow_sqTransportCost_le {μ ν ρ : Measure (Eucl d)} [IsProbabilityMeasure ν]
    {π₁ π₂ : Measure (Eucl d × Eucl d)} [IsProbabilityMeasure π₁] [IsProbabilityMeasure π₂]
    (h₁ : IsCoupling π₁ μ ν) (h₂ : IsCoupling π₂ ν ρ) :
    ∃ γ : Measure (Eucl d × Eucl d), IsCoupling γ μ ρ ∧
      sqTransportCost γ ^ (2⁻¹ : ℝ)
        ≤ sqTransportCost π₁ ^ (2⁻¹ : ℝ) + sqTransportCost π₂ ^ (2⁻¹ : ℝ) := by
  classical
  set κ₂ : Kernel (Eucl d) (Eucl d) := π₂.condKernel with hκ₂
  have hπ₂ : ν ⊗ₘ κ₂ = π₂ := by rw [hκ₂, ← h₂.1]; exact π₂.disintegrate π₂.condKernel
  set κ : Kernel (Eucl d × Eucl d) (Eucl d) := κ₂.comap Prod.snd measurable_snd with hκ
  set T : Measure ((Eucl d × Eucl d) × Eucl d) := π₁ ⊗ₘ κ with hT
  have hg₁ : Measurable (fun q : (Eucl d × Eucl d) × Eucl d => (q.1.1, q.2)) := by fun_prop
  have hg₂ : Measurable (fun q : (Eucl d × Eucl d) × Eucl d => (q.1.2, q.2)) := by fun_prop
  set γ : Measure (Eucl d × Eucl d) := T.map (fun q => (q.1.1, q.2)) with hγ
  have hTfst : T.fst = π₁ := by rw [hT]; exact Measure.fst_compProd π₁ κ
  have hm : T.map (fun q => (q.1.2, q.2)) = π₂ := by
    rw [← hπ₂]
    refine Measure.ext_of_lintegral _ fun F hF => ?_
    have hFg₂ : Measurable fun q : (Eucl d × Eucl d) × Eucl d => F (q.1.2, q.2) := hF.comp hg₂
    have hΦ : Measurable fun y => ∫⁻ z, F (y, z) ∂κ₂ y :=
      Measurable.lintegral_kernel_prod_right (κ := κ₂) (f := fun y z => F (y, z)) hF
    rw [lintegral_map hF hg₂, hT,
      Measure.lintegral_compProd hFg₂, Measure.lintegral_compProd hF]
    simp only [hκ, Kernel.comap_apply]
    rw [← h₁.2, show (π₁.snd : Measure (Eucl d)) = π₁.map Prod.snd from rfl,
      lintegral_map hΦ measurable_snd]
  have hcpl : IsCoupling γ μ ρ := by
    refine ⟨?_, ?_⟩
    · show γ.map Prod.fst = μ
      rw [hγ, Measure.map_map measurable_fst hg₁, ← h₁.1, ← hTfst]
      exact (Measure.map_map measurable_fst measurable_fst).symm
    · show γ.map Prod.snd = ρ
      rw [hγ, Measure.map_map measurable_snd hg₁, ← h₂.2, ← hm]
      exact (Measure.map_map measurable_snd hg₂).symm
  refine ⟨γ, hcpl, ?_⟩
  -- Read the three costs off the triple `T`.
  have hγcost : sqTransportCost γ = ∫⁻ q, edist q.1.1 q.2 ^ 2 ∂T := by
    rw [sqTransportCost, hγ, lintegral_map (by fun_prop) hg₁]
  have hT1 : ∫⁻ q, edist q.1.1 q.1.2 ^ 2 ∂T = sqTransportCost π₁ := by
    rw [sqTransportCost, ← hTfst,
      show (T.fst : Measure (Eucl d × Eucl d)) = T.map Prod.fst from rfl,
      lintegral_map (by fun_prop) measurable_fst]
  have hT2 : ∫⁻ q, edist q.1.2 q.2 ^ 2 ∂T = sqTransportCost π₂ := by
    rw [sqTransportCost, ← hm, lintegral_map (by fun_prop) hg₂]
  -- Minkowski (`p = 2`) applied to `f = edist x y`, `g = edist y z` on `T`.
  have hmink := ENNReal.lintegral_Lp_add_le (μ := T)
    (f := fun q => edist q.1.1 q.1.2) (g := fun q => edist q.1.2 q.2)
    (by fun_prop) (by fun_prop) one_le_two
  simp only [ENNReal.rpow_ofNat, one_div] at hmink
  rw [hγcost, ← hT1, ← hT2]
  refine le_trans ?_ hmink
  gcongr with q
  exact edist_triangle q.1.1 q.1.2 q.2

/-- **Sub-additivity of `W₂` along a gluing**: `W₂ μ ρ` is bounded by the sum of the root costs of any
plan of `(μ, ν)` and any plan of `(ν, ρ)`. -/
theorem W2_le_rpow_add {μ ν ρ : Measure (Eucl d)} [IsProbabilityMeasure ν]
    {π₁ π₂ : Measure (Eucl d × Eucl d)} [IsProbabilityMeasure π₁] [IsProbabilityMeasure π₂]
    (h₁ : IsCoupling π₁ μ ν) (h₂ : IsCoupling π₂ ν ρ) :
    W2 μ ρ ≤ sqTransportCost π₁ ^ (2⁻¹ : ℝ) + sqTransportCost π₂ ^ (2⁻¹ : ℝ) := by
  obtain ⟨γ, hγc, hγle⟩ := exists_coupling_rpow_sqTransportCost_le h₁ h₂
  exact (W2_le_rpow_sqTransportCost hγc).trans hγle

/-- **Triangle inequality for `W₂`** (probability measures): `W₂ μ ρ ≤ W₂ μ ν + W₂ ν ρ`. Descends from
the per-coupling Minkowski/gluing bound by distributing `+` through the two infima. With
`W2_self_eq_zero` and `W2_comm`, this makes `W₂` a pseudometric on probability measures. -/
theorem W2_triangle (μ ν ρ : Measure (Eucl d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ] : W2 μ ρ ≤ W2 μ ν + W2 ν ρ := by
  have key : ∀ π₁ : Measure (Eucl d × Eucl d), IsCoupling π₁ μ ν →
      ∀ π₂ : Measure (Eucl d × Eucl d), IsCoupling π₂ ν ρ →
      W2 μ ρ ≤ sqTransportCost π₁ ^ (2⁻¹ : ℝ) + sqTransportCost π₂ ^ (2⁻¹ : ℝ) := by
    intro π₁ h₁ π₂ h₂
    have hp₁ : IsProbabilityMeasure π₁ := ⟨by rw [← Measure.fst_univ, h₁.1]; exact measure_univ⟩
    have hp₂ : IsProbabilityMeasure π₂ := ⟨by rw [← Measure.fst_univ, h₂.1]; exact measure_univ⟩
    exact W2_le_rpow_add h₁ h₂
  have hrw : W2 μ ν + W2 ν ρ
      = ⨅ π₂, ⨅ (_ : IsCoupling π₂ ν ρ), ⨅ π₁, ⨅ (_ : IsCoupling π₁ μ ν),
        (sqTransportCost π₁ ^ (2⁻¹ : ℝ) + sqTransportCost π₂ ^ (2⁻¹ : ℝ)) := by
    simp only [W2, ENNReal.iInf_add, ENNReal.add_iInf]
  rw [hrw]
  exact le_iInf₂ fun π₂ h₂ => le_iInf₂ fun π₁ h₁ => key π₁ h₁ π₂ h₂

/-!
## Convexity of `W₂` under mixtures

The mixture bound `W₂(∑ aₖ Pₖ, ∑ aₖ Qₖ) ≤ ε` (when every `W₂(Pₖ, Qₖ) ≤ ε` and `∑ aₖ = 1`) rests on two
mechanical facts -- a mixture of couplings is a coupling of the mixtures, and the squared cost is
linear in the mixing measure -- plus an `ε`-approximation over the infimum: `W₂` is an infimum
(possibly unattained), so `W₂(Pₖ, Qₖ) ≤ ε` yields, for any slack `η > 0`, a coupling of root cost
`< ε + η`, not one achieving `ε` exactly.
-/

/-- A **mixture of couplings is a coupling of the mixtures**: if `πₖ` couples `(Pₖ, Qₖ)` for each `k`,
then `∑ aₖ • πₖ` couples `(∑ aₖ • Pₖ, ∑ aₖ • Qₖ)`. The marginal map `Prod.fst`/`Prod.snd` is additive
(over the finite sum) and `ℝ≥0∞`-homogeneous (`Measure.map_smul`). -/
theorem isCoupling_finset_sum_smul {M : ℕ} (a : Fin M → ℝ≥0∞)
    {π : Fin M → Measure (Eucl d × Eucl d)} {P Q : Fin M → Measure (Eucl d)}
    (h : ∀ k, IsCoupling (π k) (P k) (Q k)) :
    IsCoupling (∑ k, a k • π k) (∑ k, a k • P k) (∑ k, a k • Q k) := by
  have hmap : ∀ (g : Eucl d × Eucl d → Eucl d), Measurable g →
      (∑ k, a k • π k).map g = ∑ k, a k • (π k).map g := by
    intro g hg
    rw [← Measure.sum_fintype, Measure.map_sum hg.aemeasurable]
    simp_rw [Measure.map_smul]
    rw [Measure.sum_fintype]
  refine ⟨?_, ?_⟩
  · show (∑ k, a k • π k).map Prod.fst = ∑ k, a k • P k
    rw [hmap Prod.fst measurable_fst]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1; exact (h k).1
  · show (∑ k, a k • π k).map Prod.snd = ∑ k, a k • Q k
    rw [hmap Prod.snd measurable_snd]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1; exact (h k).2

/-- The squared transport cost is **linear in the mixing measure**:
`sqTransportCost (∑ aₖ • πₖ) = ∑ aₖ · sqTransportCost πₖ` (the lower integral splits over the finite
sum and pulls out each scalar). -/
theorem sqTransportCost_finset_sum_smul {M : ℕ} (a : Fin M → ℝ≥0∞)
    (π : Fin M → Measure (Eucl d × Eucl d)) :
    sqTransportCost (∑ k, a k • π k) = ∑ k, a k * sqTransportCost (π k) := by
  rw [sqTransportCost, lintegral_finsetSum_measure]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [lintegral_smul_measure, smul_eq_mul]
  rfl

/-- **Convexity of `W₂` under mixtures.** If `∑ aₖ = 1` and every component pair is within `ε`
(`W₂(Pₖ, Qₖ) ≤ ε`), then so is the mixture: `W₂(∑ aₖ • Pₖ, ∑ aₖ • Qₖ) ≤ ε`. Couple each pair near
optimally, mix the couplings, and bound the mixed squared cost by `ε²` via `∑ aₖ = 1` (Minkowski is
not needed -- the squared cost is already linear in the mixture). -/
theorem W2_convexCombo_le {M : ℕ} (a : Fin M → ℝ≥0∞) {P Q : Fin M → Measure (Eucl d)}
    (ha : ∑ k, a k = 1) {ε : ℝ≥0∞} (hbound : ∀ k, W2 (P k) (Q k) ≤ ε) :
    W2 (∑ k, a k • P k) (∑ k, a k • Q k) ≤ ε := by
  refine ENNReal.le_of_forall_pos_le_add fun η hη hε => ?_
  set B : ℝ≥0∞ := ε + (η : ℝ≥0∞) with hB
  have hdlt : ε < B := by
    rw [hB]; exact ENNReal.lt_add_right hε.ne (ENNReal.coe_pos.mpr hη).ne'
  -- for each component, extract a coupling of root cost `< B` (the ε-approximation)
  have hk : ∀ k, ∃ πk : Measure (Eucl d × Eucl d),
      IsCoupling πk (P k) (Q k) ∧ sqTransportCost πk ^ (2⁻¹ : ℝ) < B := fun k => by
    simpa only [W2, iInf_lt_iff, exists_prop] using (hbound k).trans_lt hdlt
  choose π hcpl hcost using hk
  have hcplγ : IsCoupling (∑ k, a k • π k) (∑ k, a k • P k) (∑ k, a k • Q k) :=
    isCoupling_finset_sum_smul a hcpl
  -- root cost `< B` gives squared cost `≤ B²`, summed against the unit weights stays `≤ B²`
  have hA : ∑ k, a k * sqTransportCost (π k) ≤ B ^ (2 : ℝ) := by
    calc ∑ k, a k * sqTransportCost (π k)
        ≤ ∑ k, a k * B ^ (2 : ℝ) := Finset.sum_le_sum fun k _ => by
          gcongr; exact (ENNReal.rpow_inv_le_iff two_pos).mp (hcost k).le
      _ = B ^ (2 : ℝ) := by rw [← Finset.sum_mul, ha, one_mul]
  calc W2 (∑ k, a k • P k) (∑ k, a k • Q k)
      ≤ sqTransportCost (∑ k, a k • π k) ^ (2⁻¹ : ℝ) := W2_le_rpow_sqTransportCost hcplγ
    _ = (∑ k, a k * sqTransportCost (π k)) ^ (2⁻¹ : ℝ) := by
          rw [sqTransportCost_finset_sum_smul]
    _ ≤ (B ^ (2 : ℝ)) ^ (2⁻¹ : ℝ) := ENNReal.rpow_le_rpow hA (by norm_num)
    _ = B := ENNReal.rpow_rpow_inv two_ne_zero B

/-!
## Finiteness of `W₂`

The `ℝ`-valued interface (`Axioms.W2 := (W2 · ·).toReal`) is only faithful where `W₂` is finite: `toReal`
sends `⊤` to `0`, so a hypothesis-free `ℝ` triangle/convexity fact about a possibly-infinite `W₂` would
be unsound. For the paper's measures -- probability measures on the unit sphere -- `W₂` is finite: the
product coupling moves mass across a distance at most the support diameter, so its squared cost is
bounded. This is the finiteness lemma the `W₂` axiom flip needs.
-/

/-- **`W₂` is finite for boundedly-supported probability measures.** If `μ` and `ν` are probability
measures a.e.-supported in the ball of radius `R` (in particular any measures on the unit sphere,
`R = 1`), the product coupling has squared cost at most `(2R)²`, so `W₂ μ ν ≠ ⊤`. -/
theorem W2_ne_top_of_ae_norm_le (μ ν : Measure (Eucl d)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {R : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ R) (hν : ∀ᵐ y ∂ν, ‖y‖ ≤ R) :
    W2 μ ν ≠ ⊤ := by
  have hae : ∀ᵐ p ∂(μ.prod ν), edist p.1 p.2 ^ 2 ≤ ENNReal.ofReal ((2 * R) ^ 2) := by
    have h1 : ∀ᵐ p ∂(μ.prod ν), ‖p.1‖ ≤ R := Measure.quasiMeasurePreserving_fst.ae hμ
    have h2 : ∀ᵐ p ∂(μ.prod ν), ‖p.2‖ ≤ R := Measure.quasiMeasurePreserving_snd.ae hν
    filter_upwards [h1, h2] with p hp1 hp2
    have hdist : dist p.1 p.2 ≤ 2 * R := by
      rw [dist_eq_norm]
      calc ‖p.1 - p.2‖ ≤ ‖p.1‖ + ‖p.2‖ := norm_sub_le _ _
        _ ≤ 2 * R := by linarith
    rw [edist_dist, ← ENNReal.ofReal_pow dist_nonneg]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [dist_nonneg (x := p.1) (y := p.2)])
  have hcost : sqTransportCost (μ.prod ν) ≤ ENNReal.ofReal ((2 * R) ^ 2) := by
    rw [sqTransportCost]
    calc ∫⁻ p, edist p.1 p.2 ^ 2 ∂(μ.prod ν)
        ≤ ∫⁻ _, ENNReal.ofReal ((2 * R) ^ 2) ∂(μ.prod ν) := lintegral_mono_ae hae
      _ = ENNReal.ofReal ((2 * R) ^ 2) := by rw [lintegral_const, measure_univ, mul_one]
  have hfin : sqTransportCost (μ.prod ν) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hcost
  have hle : W2 μ ν ≤ sqTransportCost (μ.prod ν) ^ (2⁻¹ : ℝ) :=
    W2_le_rpow_sqTransportCost (isCoupling_prod μ ν)
  exact ne_top_of_le_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hfin) hle

end MeasureToMeasure
