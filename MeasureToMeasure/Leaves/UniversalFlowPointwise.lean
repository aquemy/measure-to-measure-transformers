import MeasureToMeasure.Leaves.MeanFieldPark

/-!
# Pointwise upgrades of universal transport maps, and the parked pad block (lemma 5.4, G8)

The staging and relocation engines (`CellStagingInduction.lean`, `MergeTolerantRelocation.lean`)
conclude at the measure level, universally over all sphere-supported probability measures, and
now expose a COMMON transport map `f` with `attnMeasureFlow θ ν = ν.map f` for every such `ν`.
This file upgrades those universal measure-level statements to POINTWISE statements about `f`
itself, by instantiating them at Dirac measures: `Measure.dirac x` is a sphere-supported
probability measure supported in any set containing `x`, and `(Measure.dirac x).map f =
Measure.dirac (f x)`, so a support conclusion pins `f x` into the target set and a fixing
conclusion pins `f x = x`. This is what makes the whole-measure `lemma_5_4` assembly work even
though the flow is McKean-Vlasov: the engines' schedules are built from `V = 0` blocks, their
transport maps do not see the measure, and the Dirac instantiation extracts that fact pointwise.

Also here: the composition lemma for universal maps across schedule concatenation, and the
parked PAD block, a `pPark` block whose gate cap `{2 < ⟪e₁, ·⟫}` misses the sphere entirely, so
it fixes every sphere-supported probability measure while contributing any prescribed duration:
the exact-duration bookkeeping device of the assembly (`durationSum` padded to exactly `T`).
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory MeasureToMeasure.Foundations MeasureToMeasure.Statements
open scoped RealInnerProductSpace

variable {d : ℕ}

/-- A Dirac at a point of `S` is supported in `S` (no measurability of `S` needed). -/
theorem supportedIn_dirac {S : Set (Eucl d)} {x : Eucl d} (hx : x ∈ S) :
    supportedIn (Measure.dirac x) S := by
  refine measure_mono_null (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx)) ?_
  rw [Measure.dirac_apply' _ (measurableSet_singleton x).compl]
  simp

/-- If the pushforward of a Dirac under a map is the same Dirac, the point is fixed. -/
theorem eq_of_map_dirac_eq {f : Eucl d → Eucl d} {x : Eucl d}
    (h : (Measure.dirac x).map f = Measure.dirac x) : f x = x := by
  rw [Measure.map_dirac x] at h
  by_contra hne
  have h1 : Measure.dirac (f x) {x} = Measure.dirac x {x} := by rw [h]
  rw [Measure.dirac_apply' _ (measurableSet_singleton x),
    Measure.dirac_apply' _ (measurableSet_singleton x)] at h1
  simp only [Set.indicator_apply, Set.mem_singleton_iff, hne, if_false, if_true,
    Pi.one_apply] at h1
  exact zero_ne_one h1

/-- **Pointwise membership from a universal support conclusion.** If a schedule `θ` has the
universal transport map `f` and drives every sphere probability measure supported in `A` into a
measure supported in `B`, then `f` itself maps every sphere point of `A` into `B`. Dirac
instantiation; neither `A` nor `B` needs to be measurable. -/
theorem flow_map_mem_of_universal {θ : AttnSchedule d} {f : Eucl d → Eucl d}
    (hmap : ∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] → supportedIn ν (sphere d) →
      attnMeasureFlow θ ν = ν.map f)
    {A B : Set (Eucl d)}
    (hAB : ∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] → supportedIn ν (sphere d) →
      supportedIn ν A → supportedIn (attnMeasureFlow θ ν) B)
    {x : Eucl d} (hx : x ∈ sphere d) (hxA : x ∈ A) : f x ∈ B := by
  have hs : supportedIn (Measure.dirac x) (sphere d) := supportedIn_dirac hx
  have h := hAB (Measure.dirac x) hs (supportedIn_dirac hxA)
  rw [hmap _ hs, Measure.map_dirac x] at h
  by_contra hnB
  have h1 : Measure.dirac (f x) Bᶜ = 1 := Measure.dirac_apply_of_mem hnB
  exact one_ne_zero (h1.symm.trans h)

/-- **Pointwise fixing from a universal fixing conclusion.** If a schedule `θ` has the universal
transport map `f` and fixes the Dirac at a sphere point `x` (as the engines' fixing clauses
conclude whenever `x` clears the gates), then `f x = x`. -/
theorem flow_map_fixed_of_universal {θ : AttnSchedule d} {f : Eucl d → Eucl d}
    (hmap : ∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] → supportedIn ν (sphere d) →
      attnMeasureFlow θ ν = ν.map f)
    {x : Eucl d} (hx : x ∈ sphere d)
    (hfix : attnMeasureFlow θ (Measure.dirac x) = Measure.dirac x) : f x = x := by
  apply eq_of_map_dirac_eq
  rw [← hmap _ (supportedIn_dirac hx), hfix]

/-- **Universal maps compose across schedule concatenation.** -/
theorem universal_map_append {θ₁ θ₂ : AttnSchedule d} {f₁ f₂ : Eucl d → Eucl d}
    (hf₁m : Measurable f₁) (hf₂m : Measurable f₂)
    (h₁ : ∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] → supportedIn ν (sphere d) →
      attnMeasureFlow θ₁ ν = ν.map f₁)
    (h₂ : ∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] → supportedIn ν (sphere d) →
      attnMeasureFlow θ₂ ν = ν.map f₂) :
    ∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] → supportedIn ν (sphere d) →
      attnMeasureFlow (θ₁ ++ θ₂) ν = ν.map (f₂ ∘ f₁) := by
  intro ν _ hνs
  haveI : IsProbabilityMeasure (attnMeasureFlow θ₁ ν) :=
    isProbabilityMeasure_attnMeasureFlow θ₁ ν hνs
  have hν's : supportedIn (attnMeasureFlow θ₁ ν) (sphere d) :=
    attnMeasureFlow_supportedIn_sphere θ₁ ν hνs
  rw [attnMeasureFlow_append, h₂ (attnMeasureFlow θ₁ ν) hν's, h₁ ν hνs,
    Measure.map_map hf₂m hf₁m]

variable [NeZero d]

/-- **The parked pad block.** A `pPark` block whose gate cap `{2 < ⟪e₁, ·⟫}` misses the sphere
entirely: it fixes EVERY sphere-supported probability measure while contributing any prescribed
duration. The exact-duration bookkeeping device of the `lemma_5_4` assembly. -/
theorem exists_parked_pad_block {T : ℝ} (hT : 0 ≤ T) :
    ∃ p : AttnParams d, p.duration = T ∧
      ∀ ν : Measure (Eucl d), [IsProbabilityMeasure ν] → supportedIn ν (sphere d) →
        attnMeasureFlow [p] ν = ν := by
  refine ⟨pPark (e1 d) (e1 d) 2 T hT, pPark_duration _ _ _ _ _, ?_⟩
  intro ν _ hνs
  apply attnMeasureFlow_pPark_eq_of_off_cap (e1 d) (e1 d) 2 T hT ν hνs
  refine measure_mono_null (fun x hx => ?_) hνs
  simp only [Set.mem_setOf_eq] at hx
  intro hxs
  have hxn : ‖x‖ = 1 := norm_eq_one_of_mem_sphere hxs
  have he1 : ‖e1 d‖ = 1 := by
    rw [e1]
    rw [show ‖EuclideanSpace.single (0 : Fin d) (1 : ℝ)‖ = ‖(1 : ℝ)‖ from
      PiLp.norm_single 2 _ 0 1]
    exact norm_one
  have hcs : (⟪e1 d, x⟫ : ℝ) ≤ 1 := by
    calc (⟪e1 d, x⟫ : ℝ) ≤ ‖e1 d‖ * ‖x‖ := real_inner_le_norm _ _
      _ = 1 := by rw [he1, hxn, one_mul]
  linarith

end MeasureToMeasure.Leaves
