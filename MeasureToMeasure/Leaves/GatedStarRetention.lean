import MeasureToMeasure.Leaves.GatedChainUnion

/-!
# Several disjoint balls converging on a shared target (union-form step 3c)

The paper's Section 2 Step 3 mass-sweep (pp. 12-14) packs a connected piece with `N(δ)` disjoint
balls, then chains each packing ball toward the SAME final target -- unlike `gated_chainUnion_
retention` (union-form step 2), which chains ONE piece of mass through a LINEAR sequence of balls,
this needs `N` INDEPENDENT chains all converging on ONE shared target.

**A genuine subtlety, found and resolved by design before writing any of this leaf.** The naive
plan ("just reapply the union-tracking retention once per packing ball") runs into: a later chain's
own LAST leg has a source ball that necessarily OVERLAPS the shared target (that overlap is what
lets its own retention argument work at all), so the "identity outside union" fact alone does not
protect mass an earlier leg already delivered there -- it only protects points OUTSIDE a leg's own
union, and the shared target sits INSIDE it. This looked, at first, like it needed the elaborate
"target-preserving" machinery (`scaledGatedBlock_protect_inner_ge`, `scaledGatedBlock_z0_target_
preserved`) to trap already-delivered mass through a later leg's own push. It turns out NOT to: once
the invariant below is stated in terms of `z₁ᵒ \ Uₙ` rather than `z₁ᵒ` directly, the disjointness of
the staging balls ALONE (no trapping argument) is enough, because mass already delivered by an
earlier leg sits, region-wise, inside `Uₙ` (a subset of a PRIOR ball, disjoint from every LATER
ball's own source by hypothesis) -- so a later leg's plain "identity outside its own source" fact
already protects it, with no need to reason about where the flow actually sends any given point.

**The invariant.** `μ(z₁ᵒ \ Uₙ) + (1-ε)·μ(Uₙ) ≤ (measureFlow θ T μ)(z₁ᵒ)`, where `Uₙ := ⋃ᵢ≤ₙ ballᵢ`
and `z₁ᵒ` is the shared target. Splitting `z₁ᵒ = (z₁ᵒ \ Uₙ) ⊔ (z₁ᵒ ∩ Uₙ)` and using the identity-
outside-`Uₙ` fact on the first piece extracts the sharper `(1-ε)·μ(Uₙ) ≤ (measureFlow θ T μ)(z₁ᵒ ∩
Uₙ)` -- this is the piece that survives a later leg's run for free, since `z₁ᵒ ∩ Uₙ ⊆ Uₙ`, which is
disjoint from the new leg's source ball by hypothesis. Composing this with the new leg's OWN
`gated_twoCap_retention_localized` contribution closes the induction.

M3b/mid-level staging: union-form step 3 (of the `lemma_B_1`/`lemma_B_2` strengthening needed for
`prop_2_2`'s Step 3 construction); see the `lemma-b1-b2-union-form-campaign` project notes. Chaining
this into the FULL mass-sweep (each chain itself possibly multi-leg, not just a single staging ball)
is the next step, not yet built.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Set
open scoped ENNReal
open MeasureToMeasure

variable {d : ℕ}

/-- **`K+1` disjoint balls converge on a shared target.** Each ball `(y i, ρ i)` overlaps the shared
target `B(z₁,R₁)` on its own (`hcap`), and the balls are pairwise disjoint from EACH OTHER (`hdisj`
-- not required disjoint from the target itself, since overlapping it is the whole point). A
schedule of `K+1` switches retains, into the target, all of the mass already sitting there PLUS a
`(1-ε)` fraction of the mass in the `K+1` staging balls -- not discounting mass that was already in
the target from the start, since only the staging mass needs transporting. -/
theorem gated_star_retention (μ : Measure (Eucl d)) [IsProbabilityMeasure μ]
    (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (z₁ : Eucl d) (hz₁ : z₁ ∈ sphere d) (R₁ : ℝ) (hR₁ : R₁ ∈ Set.Ioo 0 (Real.pi / 2))
    (K : ℕ) (y : ℕ → Eucl d) (hy : ∀ i, y i ∈ sphere d) (ρ : ℕ → ℝ)
    (hρ : ∀ i, ρ i ∈ Set.Ioo 0 (Real.pi / 2))
    (hcap : ∀ i, (geodesicBall (y i) (ρ i) ∩ geodesicBall z₁ R₁).Nonempty)
    (hdisj : ∀ i j, i ≠ j → Disjoint (geodesicBall (y i) (ρ i)) (geodesicBall (y j) (ρ j))) :
    ∃ θ : Params d, switches θ ≤ K + 1 ∧
      μ (geodesicBall z₁ R₁ \ ⋃ i ≤ K, geodesicBall (y i) (ρ i)) +
        (1 - ENNReal.ofReal ε) * μ (⋃ i ≤ K, geodesicBall (y i) (ρ i)) ≤
        (Axioms.measureFlow θ T μ) (geodesicBall z₁ R₁) ∧
      ∀ x, x ∈ sphere d → x ∉ ⋃ i ≤ K, geodesicBall (y i) (ρ i) → flowMap θ T x = x := by
  induction K with
  | zero =>
    obtain ⟨ψ, hψsw, hψmass, hψfix⟩ :=
      gated_twoCap_retention_localized μ T ε hT hε (y 0) z₁ (hy 0) hz₁ (ρ 0) R₁ (hρ 0) hR₁ (hcap 0)
    have hU0 : (⋃ i ≤ 0, geodesicBall (y i) (ρ i)) = geodesicBall (y 0) (ρ 0) := by
      ext x; simp
    refine ⟨ψ, by simpa using hψsw, ?_, ?_⟩
    · rw [hU0]
      have hmeasB : MeasurableSet (geodesicBall (y 0) (ρ 0)) := measurableSet_geodesicBall _ _
      have hmeasZ : MeasurableSet (geodesicBall z₁ R₁) := measurableSet_geodesicBall _ _
      have hsplit : (Axioms.measureFlow ψ T μ) (geodesicBall z₁ R₁ \ geodesicBall (y 0) (ρ 0)) +
          (Axioms.measureFlow ψ T μ) (geodesicBall z₁ R₁ ∩ geodesicBall (y 0) (ρ 0)) =
          (Axioms.measureFlow ψ T μ) (geodesicBall z₁ R₁) := by
        rw [← measure_union Set.disjoint_sdiff_inter (hmeasZ.inter hmeasB)]
        congr 1
        rw [Set.sdiff_union_inter]
      have hfixpart : (Axioms.measureFlow ψ T μ) (geodesicBall z₁ R₁ \ geodesicBall (y 0) (ρ 0))
          = μ (geodesicBall z₁ R₁ \ geodesicBall (y 0) (ρ 0)) := by
        apply measureFlow_eq_of_flowMap_eqOn ψ hT.le μ (hmeasZ.diff hmeasB)
        intro x hx
        exact hψfix x hx.1.1 hx.2
      have hnewpart : (1 - ENNReal.ofReal ε) * μ (geodesicBall (y 0) (ρ 0)) ≤
          (Axioms.measureFlow ψ T μ) (geodesicBall z₁ R₁ ∩ geodesicBall (y 0) (ρ 0)) := by
        rw [Set.inter_comm]; exact hψmass
      calc μ (geodesicBall z₁ R₁ \ geodesicBall (y 0) (ρ 0)) +
            (1 - ENNReal.ofReal ε) * μ (geodesicBall (y 0) (ρ 0))
          ≤ (Axioms.measureFlow ψ T μ) (geodesicBall z₁ R₁ \ geodesicBall (y 0) (ρ 0)) +
            (Axioms.measureFlow ψ T μ) (geodesicBall z₁ R₁ ∩ geodesicBall (y 0) (ρ 0)) := by
            rw [hfixpart]; exact add_le_add le_rfl hnewpart
        _ = (Axioms.measureFlow ψ T μ) (geodesicBall z₁ R₁) := hsplit
    · intro x hxs hxout
      rw [hU0] at hxout
      exact hψfix x hxs hxout
  | succ n ih =>
    obtain ⟨θ, hsw, hmass, hfix⟩ := ih
    haveI := Axioms.isProbabilityMeasure_measureFlow θ T μ
    set Un := ⋃ i ≤ n, geodesicBall (y i) (ρ i) with hUndef
    set Bnp1 := geodesicBall (y (n + 1)) (ρ (n + 1)) with hBnp1def
    set z1o := geodesicBall z₁ R₁ with hz1odef
    have hUmeas : MeasurableSet Un :=
      MeasurableSet.biUnion (Set.finite_Iic n).countable
        (fun i _ => measurableSet_geodesicBall (y i) (ρ i))
    have hBmeas : MeasurableSet Bnp1 := measurableSet_geodesicBall _ _
    have hz1meas : MeasurableSet z1o := measurableSet_geodesicBall _ _
    have hdisjUn : Disjoint Un Bnp1 := by
      rw [hUndef, Set.disjoint_iUnion_left]
      intro i
      simp only [Set.disjoint_iUnion_left]
      intro hi
      exact hdisj i (n + 1) (by omega)
    obtain ⟨ψ, hψsw, hψmass, hψfix⟩ :=
      gated_twoCap_retention_localized (Axioms.measureFlow θ T μ) T ε hT hε (y (n + 1)) z₁
        (hy (n + 1)) hz₁ (ρ (n + 1)) R₁ (hρ (n + 1)) hR₁ (hcap (n + 1))
    have hballeq : (Axioms.measureFlow θ T μ) Bnp1 = μ Bnp1 := by
      apply measureFlow_eq_of_flowMap_eqOn θ hT.le μ hBmeas
      intro x hx
      exact hfix x hx.1 (Set.disjoint_right.mp hdisjUn hx)
    have hunion_eq : Un ∪ Bnp1 = ⋃ i ≤ n + 1, geodesicBall (y i) (ρ i) := by
      rw [hUndef, Set.biUnion_le_succ]
    have hUnBound : (1 - ENNReal.ofReal ε) * μ Un ≤ (Axioms.measureFlow θ T μ) (z1o ∩ Un) := by
      have hzsplit : (Axioms.measureFlow θ T μ) (z1o ∩ Un) + (Axioms.measureFlow θ T μ) (z1o \ Un) =
          (Axioms.measureFlow θ T μ) z1o := by
        rw [← measure_union Set.disjoint_sdiff_inter.symm (hz1meas.diff hUmeas)]
        congr 1
        rw [Set.inter_union_sdiff]
      have hcompl : (Axioms.measureFlow θ T μ) (z1o \ Un) = μ (z1o \ Un) := by
        apply measureFlow_eq_of_flowMap_eqOn θ hT.le μ (hz1meas.diff hUmeas)
        intro x hx
        exact hfix x hx.1.1 hx.2
      rw [hcompl] at hzsplit
      rw [← hzsplit, add_comm ((Axioms.measureFlow θ T μ) (z1o ∩ Un))] at hmass
      exact (ENNReal.add_le_add_iff_left (measure_ne_top μ (z1o \ Un))).mp hmass
    have hzoBnp1split : (Axioms.measureFlow θ T μ) (z1o \ Bnp1) =
        μ (z1o \ (Un ∪ Bnp1)) + (Axioms.measureFlow θ T μ) (z1o ∩ Un) := by
      have hpart : z1o \ Bnp1 = (z1o \ (Un ∪ Bnp1)) ∪ (z1o ∩ Un) := by
        ext x
        simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_union]
        constructor
        · rintro ⟨hz, hnb⟩
          by_cases hu : x ∈ Un
          · exact Or.inr ⟨hz, hu⟩
          · exact Or.inl ⟨hz, fun h => h.elim hu hnb⟩
        · rintro (⟨hz, hnub⟩ | ⟨hz, hu⟩)
          · exact ⟨hz, fun hb => hnub (Or.inr hb)⟩
          · exact ⟨hz, fun hb => (Set.disjoint_left.mp hdisjUn hu) hb⟩
      have hdisjpart : Disjoint (z1o \ (Un ∪ Bnp1)) (z1o ∩ Un) := by
        rw [Set.disjoint_left]
        rintro x ⟨-, hxnub⟩ ⟨-, hxu⟩
        exact hxnub (Or.inl hxu)
      rw [hpart, measure_union hdisjpart (hz1meas.inter hUmeas)]
      congr 1
      apply measureFlow_eq_of_flowMap_eqOn θ hT.le μ (hz1meas.diff (hUmeas.union hBmeas))
      intro x hx
      exact hfix x hx.1.1 (fun h => hx.2 (Or.inl h))
    have hstepnew : (Axioms.measureFlow ψ T (Axioms.measureFlow θ T μ)) (z1o \ Bnp1) =
        (Axioms.measureFlow θ T μ) (z1o \ Bnp1) := by
      apply measureFlow_eq_of_flowMap_eqOn ψ hT.le (Axioms.measureFlow θ T μ) (hz1meas.diff hBmeas)
      intro x hx
      exact hψfix x hx.1.1 hx.2
    have hzsplit2 : (Axioms.measureFlow ψ T (Axioms.measureFlow θ T μ)) (z1o \ Bnp1) +
        (Axioms.measureFlow ψ T (Axioms.measureFlow θ T μ)) (z1o ∩ Bnp1) =
        (Axioms.measureFlow ψ T (Axioms.measureFlow θ T μ)) z1o := by
      rw [← measure_union Set.disjoint_sdiff_inter (hz1meas.inter hBmeas)]
      congr 1
      rw [Set.sdiff_union_inter]
    have hnewpart : (1 - ENNReal.ofReal ε) * μ Bnp1 ≤
        (Axioms.measureFlow ψ T (Axioms.measureFlow θ T μ)) (z1o ∩ Bnp1) := by
      rw [← hballeq, Set.inter_comm]; exact hψmass
    refine ⟨Axioms.comp θ ψ, ?_, ?_, ?_⟩
    · calc switches (Axioms.comp θ ψ) ≤ switches θ + switches ψ := Axioms.switches_comp θ ψ
        _ ≤ (n + 1) + 1 := Nat.add_le_add hsw hψsw
    · rw [Axioms.measureFlow_comp, ← hunion_eq]
      have hUmeasUnion : μ (Un ∪ Bnp1) = μ Un + μ Bnp1 :=
        measure_union hdisjUn hBmeas
      calc μ (z1o \ (Un ∪ Bnp1)) + (1 - ENNReal.ofReal ε) * μ (Un ∪ Bnp1)
          = (μ (z1o \ (Un ∪ Bnp1)) + (1 - ENNReal.ofReal ε) * μ Un)
              + (1 - ENNReal.ofReal ε) * μ Bnp1 := by
            rw [hUmeasUnion, mul_add]; ring
        _ ≤ (Axioms.measureFlow θ T μ) (z1o \ Bnp1) + (1 - ENNReal.ofReal ε) * μ Bnp1 := by
            gcongr
            rw [hzoBnp1split]
            exact add_le_add le_rfl hUnBound
        _ = (Axioms.measureFlow ψ T (Axioms.measureFlow θ T μ)) (z1o \ Bnp1) +
              (1 - ENNReal.ofReal ε) * μ Bnp1 := by rw [hstepnew]
        _ ≤ (Axioms.measureFlow ψ T (Axioms.measureFlow θ T μ)) (z1o \ Bnp1) +
              (Axioms.measureFlow ψ T (Axioms.measureFlow θ T μ)) (z1o ∩ Bnp1) :=
            add_le_add le_rfl hnewpart
        _ = (Axioms.measureFlow ψ T (Axioms.measureFlow θ T μ)) z1o := hzsplit2
    · intro x hxs hxout
      rw [← hunion_eq] at hxout
      rw [Axioms.flowMap_comp]
      simp only [Function.comp_apply]
      have hxUn : x ∉ Un := fun h => hxout (Or.inl h)
      have hxBnp1 : x ∉ Bnp1 := fun h => hxout (Or.inr h)
      rw [hfix x hxs hxUn]
      exact hψfix x hxs hxBnp1

end MeasureToMeasure.Leaves
