import MeasureToMeasure.Statements.SupportedIn
import MeasureToMeasure.Leaves.OrthantBoundaryGap
import MeasureToMeasure.Foundations.SphereMeasureBridge

/-!
# A generic point of `sphere d ∩ orthant d` avoiding any finite set of directions

`exists_disentangling_balls`' colinear-insertion step (`disentangle_insert_colinear`,
`DisentangleInductionStep.lean`) needs to feed `lemma_3_3` (`Statements/MidLevel.lean`) a FAMILY
`μ₀ : Fin N → Measure (Eucl d)` satisfying `lemma_3_3`'s own unconditional
`Pairwise (fun i k => ∀ c, barycenter (μ₀ i) ≠ c • barycenter (μ₀ k))` hypothesis, while the REAL
family has one colinear pair `(j, k)` by construction (the very scenario the leaf handles). The fix
is to substitute a FRESH, "generic" probability measure at position `k` for the purposes of this
particular call -- one whose barycenter direction is a genuine point of `sphere d ∩ orthant d` that
is not a scalar multiple of any of the (finitely many) other family members' barycenters. This file
supplies that point-level existence fact, independent of any measure-family bookkeeping.

* `orthant_sphere_scalar_eq` -- two points of `sphere d ∩ orthant d` that are scalar multiples of
  each other are equal (the orthant rules out the antipodal `c = -1` case, and `‖·‖ = 1` forces
  `c = 1` otherwise). So each line through the origin meets `sphere d ∩ orthant d` in **at most one**
  point.
* `exists_orthant_sphere_avoiding` -- for `2 ≤ d` and any FINITE family of "bad" directions
  `v : ι → Eucl d`, some point of `sphere d ∩ orthant d` is not a scalar multiple of any `v i`.
  Construction: an explicit, injective `Fin (card ι + 1)`-indexed family of candidates
  `pₖ := normalize (𝟙 + t k • (e₀ - e₁))` (`t k := 1/(k+2)`, keeping the coordinate SUM invariant at
  `d`, which forces injectivity after normalizing) gives `card ι + 1` pairwise-distinct points; since
  each bad line meets `sphere d ∩ orthant d` in at most one point (the lemma above), a pigeonhole
  argument (`Fintype.not_injective_of_card_lt`) finds a surviving candidate.
* `exists_dirac_avoiding_measure` -- the measure-level wrapper Phase 1 actually plugs into
  `lemma_3_3`'s family slot: a Dirac point mass at the avoiding point, packaged as a genuine
  sphere-and-orthant-supported probability measure whose own barycenter (itself, for a Dirac)
  avoids every scalar multiple of the finitely many "bad" directions.

M3b/mid-level staging: consumed by `disentangle_insert_colinear`'s Phase 1 filler construction; see
`Statements/MainResults.lean` and the `exists-disentangling-balls-campaign` project notes.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory MeasureToMeasure MeasureToMeasure.Statements
open scoped RealInnerProductSpace

variable {d : ℕ}

/-- Two points of `sphere d ∩ orthant d` that are scalar multiples of each other coincide: `‖·‖ = 1`
forces the scalar to `±1`, and the orthant (all coordinates strictly positive) rules out `-1`, since
a point and its negation cannot both have all-positive coordinates. -/
theorem orthant_sphere_scalar_eq [NeZero d] {x y : Eucl d} (hxs : x ∈ sphere d)
    (hxo : x ∈ orthant d) (hys : y ∈ sphere d) (hyo : y ∈ orthant d) (c : ℝ) (h : x = c • y) :
    x = y := by
  have hxn : ‖x‖ = 1 := norm_eq_one_of_mem_sphere hxs
  have hyn : ‖y‖ = 1 := norm_eq_one_of_mem_sphere hys
  have hcnorm : ‖x‖ = |c| * ‖y‖ := by rw [h, norm_smul]; simp
  rw [hxn, hyn, mul_one] at hcnorm
  have hc : c = 1 ∨ c = -1 := (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hcnorm.symm
  rcases hc with hc1 | hc1
  · rw [h, hc1, one_smul]
  · exfalso
    have hy0 : 0 < y (0 : Fin d) := hyo 0
    have hx0 : 0 < x (0 : Fin d) := hxo 0
    rw [h, hc1] at hx0
    simp only [neg_smul, one_smul, PiLp.neg_apply] at hx0
    linarith

/-- **A generic point of `sphere d ∩ orthant d`, avoiding any finite set of directions.** For
`2 ≤ d` and a finite family of "bad" directions `v : ι → Eucl d`, some point of `sphere d ∩ orthant d`
is not a scalar multiple of any `v i` (for any real scalar, in particular it avoids `v i = 0` too,
since it has norm `1`). -/
theorem exists_orthant_sphere_avoiding (hd : 2 ≤ d) {ι : Type*} [Fintype ι] (v : ι → Eucl d) :
    ∃ p : Eucl d, p ∈ sphere d ∧ p ∈ orthant d ∧ ∀ i, ∀ c : ℝ, p ≠ c • v i := by
  haveI : NeZero d := ⟨by omega⟩
  have hd0 : 0 < d := lt_of_lt_of_le two_pos hd
  have hd1 : 1 < d := lt_of_lt_of_le one_lt_two hd
  set i0 : Fin d := ⟨0, hd0⟩ with hi0
  set i1 : Fin d := ⟨1, hd1⟩ with hi1
  have hne01 : i0 ≠ i1 := by simp [hi0, hi1, Fin.ext_iff]
  set v₁ : Eucl d := WithLp.toLp 2 (fun _ => (1 : ℝ)) with hv₁
  set n : ℕ := Fintype.card ι with hn
  -- the candidate family: `t k := 1/(k+2) ∈ (0, 1/2] ⊂ (0,1)`, a strictly positive, injective
  -- (over distinct `k`) real, so the coordinate nudge below stays inside the orthant.
  set t : Fin (n + 1) → ℝ := fun k => (1 : ℝ) / ((k : ℕ) + 2) with htdef
  have hknn : ∀ k : Fin (n + 1), (0 : ℝ) ≤ (k : ℕ) := fun k => Nat.cast_nonneg _
  have ht_pos : ∀ k, 0 < t k := by
    intro k; simp only [htdef]; apply div_pos one_pos; linarith [hknn k]
  have ht_lt1 : ∀ k, t k < 1 := by
    intro k
    simp only [htdef]
    rw [div_lt_one (by linarith [hknn k])]
    linarith [hknn k]
  -- `vt k := 𝟙 + t k • (e_{i0} - e_{i1})`: a coordinate-sum-preserving nudge (sum stays `d`), which
  -- keeps every coordinate strictly positive and makes `k ↦ normalize (vt k)` injective.
  set vt : Fin (n + 1) → Eucl d :=
    fun k => v₁ + (t k) • (EuclideanSpace.single i0 (1 : ℝ) - EuclideanSpace.single i1 (1 : ℝ))
    with hvtdef
  have hv₁c : ∀ i : Fin d, v₁ i = 1 := fun i => rfl
  have hvt_i0 : ∀ k, vt k i0 = 1 + t k := by
    intro k; simp [hvtdef, hv₁, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, hne01]
  have hvt_i1 : ∀ k, vt k i1 = 1 - t k := by
    intro k
    simp [hvtdef, hv₁, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, hne01.symm]; ring
  have hvt_other : ∀ k, ∀ i, i ≠ i0 → i ≠ i1 → vt k i = 1 := by
    intro k i hi0' hi1'
    simp [hvtdef, hv₁, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, hi0', hi1']
  have hpos : ∀ k, ∀ i, 0 < vt k i := by
    intro k i
    by_cases h0 : i = i0
    · rw [h0, hvt_i0]; linarith [ht_pos k]
    · by_cases h1 : i = i1
      · rw [h1, hvt_i1]; linarith [ht_lt1 k]
      · rw [hvt_other k i h0 h1]; norm_num
  have hvtne0 : ∀ k, vt k ≠ 0 := by
    intro k h
    have := hpos k i0
    rw [h] at this
    simp at this
  have hvtnorm : ∀ k, 0 < ‖vt k‖ := fun k => norm_pos_iff.mpr (hvtne0 k)
  set p : Fin (n + 1) → Eucl d := fun k => ‖vt k‖⁻¹ • vt k with hpdef
  have hpnorm : ∀ k, ‖p k‖ = 1 := fun k => norm_smul_inv_norm (hvtne0 k)
  have hppos : ∀ k, ∀ i, 0 < p k i := by
    intro k i
    have heq : p k i = ‖vt k‖⁻¹ * vt k i := rfl
    rw [heq]
    exact mul_pos (inv_pos.mpr (hvtnorm k)) (hpos k i)
  have hps : ∀ k, p k ∈ sphere d := by
    intro k; rw [sphere, Metric.mem_sphere, dist_zero_right]; exact hpnorm k
  have hpo : ∀ k, p k ∈ orthant d := fun k i => hppos k i
  have hsum : ∀ k, ∑ i, vt k i = (d : ℝ) := by
    intro k
    simp [hvtdef, hv₁, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, mul_sub]
  have hsmulsum : ∀ (c : ℝ) (w : Eucl d), ∑ i, (c • w) i = c * ∑ i, w i := by
    intro c w; simp [PiLp.smul_apply, Finset.mul_sum]
  -- `p` is injective: two equal-image indices force equal `vt`-values (via the sum invariant
  -- pinning the scalar factor to `1`), hence equal `t`-values, hence equal indices.
  have hpinj : Function.Injective p := by
    intro k1 k2 heq
    have hscaled : vt k1 = (‖vt k1‖ * ‖vt k2‖⁻¹) • vt k2 := by
      have h1 : (‖vt k1‖ • p k1 : Eucl d) = ‖vt k1‖ • p k2 := by rw [heq]
      rw [hpdef] at h1
      simp only [smul_smul] at h1
      rw [mul_inv_cancel₀ (hvtnorm k1).ne', one_smul] at h1
      exact h1
    have step1 := congrArg (fun w : Eucl d => ∑ i, w i) hscaled
    simp only at step1
    have step2 := hsmulsum (‖vt k1‖ * ‖vt k2‖⁻¹) (vt k2)
    rw [hsum k1, step2, hsum k2] at step1
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd0
    have hscalar1 : (‖vt k1‖ * ‖vt k2‖⁻¹) = 1 := by nlinarith [step1]
    rw [hscalar1, one_smul] at hscaled
    have h0 : vt k1 i0 = vt k2 i0 := by rw [hscaled]
    rw [hvt_i0 k1, hvt_i0 k2] at h0
    have ht_eq : t k1 = t k2 := by linarith
    simp only [htdef] at ht_eq
    have hne1 : ((k1 : ℕ) : ℝ) + 2 ≠ 0 := by linarith [hknn k1]
    have hne2 : ((k2 : ℕ) : ℝ) + 2 ≠ 0 := by linarith [hknn k2]
    rw [div_eq_div_iff hne1 hne2] at ht_eq
    have hkeq : ((k1 : ℕ) : ℝ) = ((k2 : ℕ) : ℝ) := by nlinarith [ht_eq]
    have hkeqn : (k1 : ℕ) = (k2 : ℕ) := by exact_mod_cast hkeq
    exact Fin.ext hkeqn
  -- pigeonhole: `n + 1` pairwise-distinct candidates against `n` bad directions, each of which
  -- eliminates at most one candidate (`orthant_sphere_scalar_eq`), leaves a survivor.
  by_contra hcon
  push Not at hcon
  have hex : ∀ k, ∃ i, ∃ c : ℝ, p k = c • v i := by
    intro k
    obtain ⟨i, c, hic⟩ := hcon (p k) (hps k) (hpo k)
    exact ⟨i, c, hic⟩
  choose wit c hwc using hex
  have hnotinj : ¬ Function.Injective wit := by
    apply Fintype.not_injective_of_card_lt
    simp [hn]
  rw [Function.not_injective_iff] at hnotinj
  obtain ⟨k1, k2, hwiteq, hk12⟩ := hnotinj
  have hpk1ne0 : p k1 ≠ 0 := by
    intro h; have := hpnorm k1; rw [h] at this; simp at this
  have hc1ne0 : c k1 ≠ 0 := by
    intro h; apply hpk1ne0; rw [hwc k1, h, zero_smul]
  have hveq : v (wit k1) = (c k1)⁻¹ • p k1 := by
    rw [hwc k1, smul_smul, inv_mul_cancel₀ hc1ne0, one_smul]
  have hp2v : p k2 = (c k2 * (c k1)⁻¹) • p k1 := by
    rw [hwc k2, ← hwiteq, hveq, smul_smul]
  have hpk1k2 : p k2 = p k1 :=
    orthant_sphere_scalar_eq (hps k2) (hpo k2) (hps k1) (hpo k1) _ hp2v
  exact hk12 (hpinj hpk1k2.symm)

/-- **A placeholder probability measure avoiding a finite set of directions.** The measure-level
wrapper `exists_disentangling_balls`'s Phase 1 filler actually needs: a Dirac point mass at
`exists_orthant_sphere_avoiding`'s point is a genuine sphere-and-orthant-supported probability
measure whose own barycenter (a Dirac's barycenter is just the point itself,
`MeasureTheory.integral_dirac`) avoids every scalar multiple of the finitely many "bad" directions
`v i`. Substituting this measure at the colinear pair's new-member slot lets `lemma_3_3`'s blanket
`hnoncol` hypothesis survive over the WHOLE family even though the true family has exactly one
colinear pair there -- the true member's own fate is read off separately, through `lemma_3_3`'s
companion argument, not through this filler slot. -/
theorem exists_dirac_avoiding_measure (hd : 2 ≤ d) {ι : Type*} [Fintype ι] (v : ι → Eucl d) :
    ∃ ρ : Measure (Eucl d), IsProbabilityMeasure ρ ∧ ρ (sphere d)ᶜ = 0 ∧ ρ (orthant d)ᶜ = 0 ∧
      ∀ i, ∀ c : ℝ, barycenter ρ ≠ c • v i := by
  obtain ⟨p, hps, hpo, hpavoid⟩ := exists_orthant_sphere_avoiding hd v
  refine ⟨Measure.dirac p, MeasureTheory.Measure.dirac.isProbabilityMeasure, ?_, ?_, ?_⟩
  · rw [MeasureTheory.Measure.dirac_apply' _ (measurableSet_sphere d).compl]
    simp [hps]
  · rw [MeasureTheory.Measure.dirac_apply' _ isOpen_orthant.measurableSet.compl]
    simp [hpo]
  · have hbary : barycenter (Measure.dirac p) = p := MeasureTheory.integral_dirac (fun x => x) p
    rw [hbary]
    exact hpavoid

end MeasureToMeasure.Leaves
