import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import MeasureToMeasure.Foundations.Sphere

/-!
# Leaf L3-collapse-2 (Lemma 3.4 Part 1): the rim annulus carries vanishing mass

The `W₂` collapse of App. B.3 Part 1 concentrates the *open* gate cap `{⟪ω,·⟫ > cos R}` onto the pole
`ω`. `gatedBlock_mapsTo_cap` gives a **uniform** reach only on the closed sub-cap `{⟪ω,·⟫ ≥ m}` with
`m > cos R`, so the "rim annulus" `A_m = {cos R < ⟪ω,·⟫ < m}` is moved but not collapsed. The
displacement integral over `A_m` is bounded only by the crude diameter `‖·‖² ≤ 4`, so the collapse
error carries a term `4·μ(A_m)`.

This leaf supplies the missing control: **`μ(A_m)` can be made arbitrarily small by taking `m ↓ cos R`.**
No atom/null-boundary bookkeeping is needed — the annulus is open at `cos R`, so the family `A_m`
shrinks to `∅` as `m ↓ cos R`, and continuity of a finite measure from above
(`tendsto_measure_iInter_atTop`) sends `μ(A_m) → 0`. (The boundary sphere `{⟪ω,·⟫ = cos R}` is not in
any `A_m`; in the assembly it lies in the *parked* region where `flowMap = id`, contributing `0`
regardless of its mass.)
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ENNReal

variable {d : ℕ}

/-- **L3-collapse-2.** For a finite measure `μ` on `Eucl d`, a unit pole `ω`, and a gate threshold
`cos R < 1`, the rim annulus `{x | cos R < ⟪ω,x⟫ < m}` has mass `≤ ε` for some `m` strictly between
`cos R` and `1`. As `m ↓ cos R` the annuli shrink to `∅`, so continuity of measure from above forces
their mass to `0`; this is the annulus half of the single-block `W₂` collapse error. -/
theorem exists_annulus_measure_le {ω : Eucl d} {cosR : ℝ} (hcosR1 : cosR < 1)
    {μ : Measure (Eucl d)} [IsFiniteMeasure μ] {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ m : ℝ, cosR < m ∧ m < 1 ∧
      μ {x | cosR < (⟪ω, x⟫ : ℝ) ∧ (⟪ω, x⟫ : ℝ) < m} ≤ ε := by
  have h1c : (0 : ℝ) < 1 - cosR := by linarith
  -- a sequence of thresholds decreasing to `cos R`, all strictly inside `(cos R, 1)`
  set mseq : ℕ → ℝ := fun k => cosR + (1 - cosR) / ((k : ℝ) + 2) with hmseq
  have hk2pos : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 2 := fun k => by positivity
  have hmpos : ∀ k, cosR < mseq k := by
    intro k; have : (0 : ℝ) < (1 - cosR) / ((k : ℝ) + 2) := by positivity
    simp only [hmseq]; linarith
  have hmlt1 : ∀ k, mseq k < 1 := by
    intro k
    have hden : (1 : ℝ) < (k : ℝ) + 2 := by have := (Nat.cast_nonneg k : (0:ℝ) ≤ k); linarith
    have : (1 - cosR) / ((k : ℝ) + 2) < 1 - cosR := div_lt_self h1c hden
    simp only [hmseq]; linarith
  have hmanti : Antitone mseq := by
    intro k k' hkk'
    have hle : ((k : ℝ) + 2) ≤ ((k' : ℝ) + 2) := by
      have := (Nat.cast_le.mpr hkk' : (k : ℝ) ≤ k'); linarith
    simp only [hmseq]
    gcongr
  have htendm : Tendsto mseq atTop (nhds cosR) := by
    have h0 : Tendsto (fun k : ℕ => (1 - cosR) / ((k : ℝ) + 2)) atTop (nhds 0) :=
      Tendsto.div_atTop tendsto_const_nhds
        (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    have := (tendsto_const_nhds (x := cosR)).add h0
    simpa only [hmseq, add_zero] using this
  -- the shrinking annuli
  set s : ℕ → Set (Eucl d) := fun k => {x | cosR < (⟪ω, x⟫ : ℝ) ∧ (⟪ω, x⟫ : ℝ) < mseq k} with hs
  have hcont : Continuous (fun x : Eucl d => (⟪ω, x⟫ : ℝ)) := continuous_const.inner continuous_id
  have hmeas : ∀ k, MeasurableSet (s k) := by
    intro k
    have hpre : s k = (fun x : Eucl d => (⟪ω, x⟫ : ℝ)) ⁻¹' Set.Ioo cosR (mseq k) := by
      ext x; simp only [hs, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioo]
    rw [hpre]; exact hcont.measurable measurableSet_Ioo
  have hanti : Antitone s := by
    intro k k' hkk' x hx
    exact ⟨hx.1, lt_of_lt_of_le hx.2 (hmanti hkk')⟩
  have hInter : (⋂ k, s k) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    rw [Set.mem_iInter] at hx
    have hlo : cosR < (⟪ω, x⟫ : ℝ) := (hx 0).1
    have hle : (⟪ω, x⟫ : ℝ) ≤ cosR :=
      ge_of_tendsto htendm (Filter.Eventually.of_forall (fun k => (hx k).2.le))
    linarith
  -- continuity of measure from above: `μ (s k) → μ (⋂ k, s k) = 0`
  have htendμ : Tendsto (fun k => μ (s k)) atTop (nhds (μ (⋂ k, s k))) :=
    tendsto_measure_iInter_atTop (fun k => (hmeas k).nullMeasurableSet) hanti
      ⟨0, measure_ne_top μ _⟩
  rw [hInter, measure_empty] at htendμ
  obtain ⟨N, hN⟩ := (ENNReal.tendsto_atTop_zero.mp htendμ) ε hε
  exact ⟨mseq N, hmpos N, hmlt1 N, hN N le_rfl⟩

end MeasureToMeasure.Leaves
