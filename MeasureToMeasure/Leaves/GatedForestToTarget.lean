import MeasureToMeasure.Leaves.GatedChainForest
import MeasureToMeasure.Leaves.GatedStarRetention

/-!
# Several disjoint multi-leg chains converging on a shared target (union-form step 3e)

The final assembly of the union-form campaign: composing `gated_chainForest_retention` (`N+1`
disjoint linear chains, each possibly several legs long) with `gated_star_retention` (`N+1` staging
balls converging on a shared target) gives the full shape of the paper's Section 2 Step 3
mass-sweep -- pack a connected piece with disjoint balls, chain each toward a shared target, where a
packing ball may be far enough from the target to need an intermediate chain rather than a single
leg.

**The assembly.** Run `θ_chains` (`gated_chainForest_retention`) first, landing each arm's own mass
in that arm's own last ball; then `θ_star` (`gated_star_retention`), applied to the EVOLVED measure
with each arm's last ball as its "staging ball", pushing everything into the shared target. Two
things must be checked, neither automatic from the two pieces alone:

* **A genuinely new hypothesis is needed** (`hdisjTarget`): the target must be disjoint from every
  NON-last ball of every arm -- only touching each arm's own endpoint. Nothing in the two composed
  theorems implies this; without it, the target could overlap an arm's *interior*, and the forest's
  own "identity outside" fact (needed to know the untouched part of the target survives the chain
  step) would not cover exactly the right set.
* **Switch budget is additive per arm, not `(ΣLᵢ)+1`.** Each arm contributes its own `Lᵢ` internal
  legs plus one final leg into the target, so the total is `Σᵢ(Lᵢ+1)`, not a single extra switch
  shared across all arms (an error caught by the type-checker while assembling this, not spotted in
  the earlier hand-derived design).
* **Discounts stay additive across arms.** Each arm keeps its own `(1-ε)^{Lᵢ+1}` power (chain depth
  plus the one star step) -- summed, not compounded into one uniform power, exactly as
  `gated_star_retention`'s own single-leg version does for depth 1.

M3b/mid-level staging: this completes the `lemma_B_1`/`lemma_B_2` union-form strengthening needed
for `prop_2_2`'s Step 3 (ball packing via Vitali/Besicovitch covering, path-connected chaining
construction, and the ε,δ,η→0 Wasserstein-duality limit remain untouched -- a separate, larger
follow-up campaign); see the `lemma-b1-b2-union-form-campaign` project notes.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Set
open scoped ENNReal
open MeasureToMeasure

variable {d : ℕ}

/-- **`N+1` disjoint multi-leg chains converge on a shared target.** Each arm `i` is its own linear
chain of `L i + 1` balls (`z i 0, …, z i (L i)`, per `gated_chainUnion_retention`'s own structure;
`hchain`/`hdisjWithin` bounded per-arm by `L i`, matching `gated_chainForest_retention`'s own
bounded form -- see that file's module docstring for why the unbounded form is unsatisfiable),
pairwise disjoint across arms (`hdisjAcross`); the target overlaps only each arm's own LAST ball
(`hcapTarget`) and is disjoint from every earlier ball of every arm (`hdisjTarget`, the "well-formed
chain" hypothesis this composition needs beyond the two pieces it's built from). A schedule of
`Σᵢ(Lᵢ+1)` switches retains all mass already in the target plus a `(1-ε)^{Lᵢ+1}`-discounted fraction
of each arm's own chain-union mass, summed across arms. -/
theorem gated_forest_to_target_retention (μ : Measure (Eucl d)) [IsProbabilityMeasure μ]
    (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (z₁ : Eucl d) (hz₁ : z₁ ∈ sphere d) (R₁ : ℝ) (hR₁ : R₁ ∈ Set.Ioo 0 (Real.pi / 2))
    (N : ℕ) (L : ℕ → ℕ) (z : ℕ → ℕ → Eucl d) (R : ℕ → ℕ → ℝ)
    (hz : ∀ i j, z i j ∈ sphere d) (hR : ∀ i j, R i j ∈ Set.Ioo 0 (Real.pi / 2))
    (hchain : ∀ i k, k < L i →
      (geodesicBall (z i k) (R i k) ∩ geodesicBall (z i (k + 1)) (R i (k + 1))).Nonempty)
    (hdisjWithin : ∀ i j k, j + 2 ≤ k → k ≤ L i →
      Disjoint (geodesicBall (z i j) (R i j)) (geodesicBall (z i k) (R i k)))
    (hdisjAcross : ∀ i i' j j', i ≠ i' →
      Disjoint (geodesicBall (z i j) (R i j)) (geodesicBall (z i' j') (R i' j')))
    (hcapTarget : ∀ i, (geodesicBall (z i (L i)) (R i (L i)) ∩ geodesicBall z₁ R₁).Nonempty)
    (hdisjTarget : ∀ i, ∀ j < L i,
      Disjoint (geodesicBall (z i j) (R i j)) (geodesicBall z₁ R₁)) :
    ∃ θ : Params d, switches θ ≤ ∑ i ∈ Finset.Iic N, (L i + 1) ∧
      μ (geodesicBall z₁ R₁ \ ⋃ i ≤ N, geodesicBall (z i (L i)) (R i (L i))) +
        ∑ i ∈ Finset.Iic N, (1 - ENNReal.ofReal ε) ^ (L i + 1) *
          μ (⋃ j ≤ L i, geodesicBall (z i j) (R i j)) ≤
        (Axioms.measureFlow θ T μ) (geodesicBall z₁ R₁) := by
  obtain ⟨θc, hcsw, hcmass, hcfix⟩ :=
    gated_chainForest_retention μ T ε hT hε N L z R hz hR hchain hdisjWithin hdisjAcross
  haveI := Axioms.isProbabilityMeasure_measureFlow θc T μ
  obtain ⟨θs, hssw, hsmass, hsfix⟩ :=
    gated_star_retention (Axioms.measureFlow θc T μ) T ε hT hε z₁ hz₁ R₁ hR₁ N
      (fun i => z i (L i)) (fun i => hz i (L i)) (fun i => R i (L i)) (fun i => hR i (L i))
      hcapTarget (fun i i' hne => hdisjAcross i i' (L i) (L i') hne)
  set arms := ⋃ i ≤ N, geodesicBall (z i (L i)) (R i (L i)) with harmsdef
  set forest := ⋃ i ≤ N, ⋃ j ≤ L i, geodesicBall (z i j) (R i j) with hforestdef
  have hsumbound : ∑ i ∈ Finset.Iic N, (1 - ENNReal.ofReal ε) ^ (L i) *
      μ (⋃ j ≤ L i, geodesicBall (z i j) (R i j)) ≤
      (Axioms.measureFlow θc T μ) arms := by
    have hmeasarms : (Axioms.measureFlow θc T μ) arms =
        ∑ i ∈ Finset.Iic N, (Axioms.measureFlow θc T μ) (geodesicBall (z i (L i)) (R i (L i))) := by
      rw [harmsdef]
      have hconv : (⋃ i ≤ N, geodesicBall (z i (L i)) (R i (L i))) =
          ⋃ i ∈ Finset.Iic N, geodesicBall (z i (L i)) (R i (L i)) := by ext x; simp
      rw [hconv]
      apply measure_biUnion_finset
      · intro i _ i' _ hne
        exact hdisjAcross i i' (L i) (L i') hne
      · intro i _
        exact measurableSet_geodesicBall _ _
    rw [hmeasarms]
    exact Finset.sum_le_sum (fun i hi => hcmass i (Finset.mem_Iic.mp hi))
  have htargetsub : (geodesicBall z₁ R₁ \ arms) ⊆ forestᶜ := by
    rw [harmsdef, hforestdef]
    rintro x ⟨hxt, hxna⟩ hxf
    apply hxna
    simp only [Set.mem_iUnion] at hxf
    obtain ⟨i, hiN, j, hjLi, hxj⟩ := hxf
    rcases Nat.lt_or_ge j (L i) with hjlt | hjge
    · exact absurd hxj (Set.disjoint_right.mp (hdisjTarget i j hjlt) hxt)
    · have heq : j = L i := le_antisymm hjLi hjge
      rw [heq] at hxj
      simp only [Set.mem_iUnion]
      exact ⟨i, hiN, hxj⟩
  have htargeteq : (Axioms.measureFlow θc T μ) (geodesicBall z₁ R₁ \ arms) =
      μ (geodesicBall z₁ R₁ \ arms) := by
    apply measureFlow_eq_of_flowMap_eqOn θc hT.le μ
      ((measurableSet_geodesicBall z₁ R₁).diff (by
        rw [harmsdef]
        exact MeasurableSet.biUnion (Set.finite_Iic N).countable
          (fun i _ => measurableSet_geodesicBall _ _)))
    intro x hx
    exact hcfix x hx.1.1 (htargetsub hx)
  have hscale : (1 - ENNReal.ofReal ε) * ∑ i ∈ Finset.Iic N, (1 - ENNReal.ofReal ε) ^ (L i) *
      μ (⋃ j ≤ L i, geodesicBall (z i j) (R i j)) =
      ∑ i ∈ Finset.Iic N, (1 - ENNReal.ofReal ε) ^ (L i + 1) *
        μ (⋃ j ≤ L i, geodesicBall (z i j) (R i j)) := by
    rw [Finset.mul_sum]
    congr 1
    ext i
    rw [pow_succ']
    ring
  refine ⟨Axioms.comp θc θs, ?_, ?_⟩
  · have hsumsplit : ∑ i ∈ Finset.Iic N, (L i + 1) = (∑ i ∈ Finset.Iic N, L i) + (N + 1) := by
      rw [Finset.sum_add_distrib]
      simp
    rw [hsumsplit]
    exact (Axioms.switches_comp θc θs).trans (Nat.add_le_add hcsw hssw)
  · rw [Axioms.measureFlow_comp]
    calc μ (geodesicBall z₁ R₁ \ arms) +
          ∑ i ∈ Finset.Iic N, (1 - ENNReal.ofReal ε) ^ (L i + 1) *
            μ (⋃ j ≤ L i, geodesicBall (z i j) (R i j))
        = (Axioms.measureFlow θc T μ) (geodesicBall z₁ R₁ \ arms) +
            (1 - ENNReal.ofReal ε) * ∑ i ∈ Finset.Iic N, (1 - ENNReal.ofReal ε) ^ (L i) *
              μ (⋃ j ≤ L i, geodesicBall (z i j) (R i j)) := by rw [htargeteq, hscale]
      _ ≤ (Axioms.measureFlow θc T μ) (geodesicBall z₁ R₁ \ arms) +
            (1 - ENNReal.ofReal ε) * (Axioms.measureFlow θc T μ) arms := by
          gcongr
      _ ≤ (Axioms.measureFlow θs T (Axioms.measureFlow θc T μ)) (geodesicBall z₁ R₁) := hsmass

end MeasureToMeasure.Leaves
