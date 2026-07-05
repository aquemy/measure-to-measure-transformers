import MeasureToMeasure.Leaves.BesicovitchTarget
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms

/-!
# Leaf (Lemma 3.4 Part 1, Path I assembly): a mass-gap **cap** inside the carrier

Turns the Besicovitch mass-gap ball (`exists_mem_eventually_closedBall_measure_ne`) into exactly the
object the App. B.3 collapse gates on: a **spherical cap** `{cos R < ⟪z, ·⟫}` with `z ∈ 𝕊`, whose
sphere-trace lies inside the open carrier `U` and on which the two measures still differ.

Two conversions do it, both riding on sphere support (`μ (𝕊ᶜ) = 0`):
* **ball ↦ cap.** On the sphere `‖x − z‖ ≤ r ⟺ ⟪z, x⟫ ≥ 1 − r²/2`, so the closed ball's sphere-trace
  is the closed cap at `cos R = 1 − r²/2`; sphere support turns the ball mass into the cap mass.
* **closed ↦ strict.** The gate is active on the *strict* cap `{cos R < ⟪z, ·⟫}` (the boundary latitude
  `{⟪z, ·⟫ = cos R}` is parked), so we need the *strict* cap mass. Choosing `cos R` off the countable
  set of latitudes that carry mass (`countable_meas_level_set_pos`) makes the boundary null, so the
  strict and closed caps have equal mass.

`cos R` is chosen in `(cLow, 1)` — close enough to `1` that `r = √(2(1 − cos R))` beats both the
Besicovitch gap radius and the carrier's inradius at `z` — and off the countable bad-latitude set, via
`Set.Countable.dense_compl`. The resulting `cos R ∈ (1/2, 1)` (a *small* cap, needed downstream so every cap point is close),
`cap ∩ 𝕊 ⊆ U`, `μ(cap) ≠ ν(cap)`.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace ENNReal

variable {d : ℕ}

/-- **Mass-gap cap inside the carrier.** For distinct finite measures supported on the sphere and on
an open carrier `U`, some sphere direction `z` and threshold `cos R ∈ (1/2, 1)` give a cap whose
sphere-trace sits in `U` and on which `μ` and `ν` differ:
`μ {x | cos R < ⟪z, x⟫} ≠ ν {x | cos R < ⟪z, x⟫}`. Besicovitch mass-gap ball (centred in `U ∩ 𝕊`)
converted to a strict cap via sphere support and a null-latitude choice of `cos R`. -/
theorem exists_cap_measure_ne_subset {μ ν : Measure (Eucl d)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hne : μ ≠ ν) {U : Set (Eucl d)} (hUopen : IsOpen U)
    (hμU : μ Uᶜ = 0) (hνU : ν Uᶜ = 0) (hμs : μ (sphere d)ᶜ = 0) (hνs : ν (sphere d)ᶜ = 0) :
    ∃ (z : Eucl d) (cosR : ℝ), z ∈ sphere d ∧ 1 / 2 < cosR ∧ cosR < 1 ∧
      (∀ x ∈ sphere d, cosR < (⟪z, x⟫ : ℝ) → x ∈ U) ∧
      μ {x | cosR < (⟪z, x⟫ : ℝ)} ≠ ν {x | cosR < (⟪z, x⟫ : ℝ)} := by
  -- the Besicovitch ball, centred in `W = U ∩ 𝕊`
  have hW : (μ + ν) (U ∩ sphere d)ᶜ = 0 := by
    rw [Set.compl_inter]
    refine measure_union_null ?_ ?_ <;> simp_all [Measure.add_apply]
  obtain ⟨z, hzW, hev⟩ := exists_mem_eventually_closedBall_measure_ne hne hW
  obtain ⟨hzU, hzS⟩ := hzW
  have hznorm : ‖z‖ = 1 := norm_eq_one_of_mem_sphere hzS
  -- extract a right-interval of gap radii and the carrier inradius at `z`
  obtain ⟨rb, hrb0, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp hev
  rw [Set.mem_Ioi] at hrb0
  obtain ⟨rU, hrU0, hUball⟩ := Metric.isOpen_iff.mp hUopen z hzU
  -- ρ-a.e. sphere membership, and the countable set of latitudes that carry mass
  have hμs_ae : ∀ᵐ x ∂μ, x ∈ sphere d := ae_iff.mpr hμs
  have hνs_ae : ∀ᵐ x ∂ν, x ∈ sphere d := ae_iff.mpr hνs
  have hgmeas : Measurable (fun x : Eucl d => (⟪z, x⟫ : ℝ)) :=
    (continuous_const.inner continuous_id).measurable
  set badC : Set ℝ :=
    {c | 0 < μ {x | (⟪z, x⟫ : ℝ) = c}} ∪ {c | 0 < ν {x | (⟪z, x⟫ : ℝ) = c}} with hbadCdef
  have hbadC : badC.Countable :=
    (Measure.countable_meas_level_set_pos hgmeas).union (Measure.countable_meas_level_set_pos hgmeas)
  -- pick `cos R` close to `1` (so `r` is small) and off the null-latitude bad set
  set cLow : ℝ := max (1 / 2) (max (1 - rb ^ 2 / 2) (1 - rU ^ 2 / 2)) with hcLowdef
  have hcLow1 : cLow < 1 := by
    rw [hcLowdef]
    refine max_lt (by norm_num) (max_lt ?_ ?_) <;>
      nlinarith [mul_pos hrb0 hrb0, mul_pos hrU0 hrU0]
  obtain ⟨cosR, hcosRIoo, hcosRbad⟩ :=
    (hbadC.dense_compl ℝ).inter_open_nonempty (Set.Ioo cLow 1) isOpen_Ioo
      ⟨(cLow + 1) / 2, by nlinarith, by nlinarith⟩
  obtain ⟨hcosRlow, hcosR1⟩ := hcosRIoo
  have hcosR_half : 1 / 2 < cosR := lt_of_le_of_lt (le_max_left _ _) hcosRlow
  have hcosR0 : 0 ≤ cosR := by linarith
  -- the corresponding radius `r = √(2(1 − cos R))`
  set r : ℝ := Real.sqrt (2 * (1 - cosR)) with hrdef
  have h2c : (0 : ℝ) ≤ 2 * (1 - cosR) := by nlinarith
  have hr2 : r ^ 2 = 2 * (1 - cosR) := Real.sq_sqrt h2c
  have hrpos : 0 < r := Real.sqrt_pos.mpr (by nlinarith)
  -- `r` beats the gap radius and the inradius
  have hcosR_rb : 1 - rb ^ 2 / 2 < cosR :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right (1 / 2 : ℝ) _)) hcosRlow
  have hcosR_rU : 1 - rU ^ 2 / 2 < cosR :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right (1 / 2 : ℝ) _)) hcosRlow
  have hr_rb : r < rb := by
    have : r ^ 2 < rb ^ 2 := by rw [hr2]; nlinarith
    have := abs_lt_of_sq_lt_sq this hrb0.le
    rwa [abs_of_nonneg hrpos.le] at this
  have hr_rU : r < rU := by
    have : r ^ 2 < rU ^ 2 := by rw [hr2]; nlinarith
    have := abs_lt_of_sq_lt_sq this hrU0.le
    rwa [abs_of_nonneg hrpos.le] at this
  -- the ball-mass gap at this radius
  have hgap : μ (closedBall z r) ≠ ν (closedBall z r) := hsub ⟨hrpos, hr_rb⟩
  -- both latitudes at `cos R` are null
  have hlat : ∀ ρ : Measure (Eucl d), IsFiniteMeasure ρ →
      cosR ∉ {c | 0 < ρ {x | (⟪z, x⟫ : ℝ) = c}} → ρ {x | (⟪z, x⟫ : ℝ) = cosR} = 0 := by
    intro ρ _ h
    simp only [Set.mem_setOf_eq, not_lt, nonpos_iff_eq_zero] at h
    exact h
  have hcosRbad' : cosR ∉ badC := hcosRbad
  rw [hbadCdef, Set.mem_union, not_or] at hcosRbad'
  have hlatμ : μ {x | (⟪z, x⟫ : ℝ) = cosR} = 0 := hlat μ ‹_› hcosRbad'.1
  have hlatν : ν {x | (⟪z, x⟫ : ℝ) = cosR} = 0 := hlat ν ‹_› hcosRbad'.2
  -- the strict cap ↦ closed ball mass identity, for a sphere-supported finite measure
  have hcapball : ∀ (ρ : Measure (Eucl d)), ρ (sphere d)ᶜ = 0 →
      ρ {x | (⟪z, x⟫ : ℝ) = cosR} = 0 →
      ρ {x | cosR < (⟪z, x⟫ : ℝ)} = ρ (closedBall z r) := by
    intro ρ hρs hρlat
    have hρs_ae : ∀ᵐ x ∂ρ, x ∈ sphere d := ae_iff.mpr hρs
    -- `ρ A = ρ (A ∩ 𝕊)`
    have hAS : ∀ A : Set (Eucl d), ρ A = ρ (A ∩ sphere d) := by
      intro A; apply measure_congr; rw [Filter.eventuallyEq_set]
      filter_upwards [hρs_ae] with x hx; simp [hx]
    -- strict cap and closed cap agree up to the null latitude
    have hsub_cap : {x | cosR < (⟪z, x⟫ : ℝ)} ⊆ {x | cosR ≤ (⟪z, x⟫ : ℝ)} :=
      Set.setOf_subset_setOf.2 fun _ h => h.le
    have hdiff : {x | cosR ≤ (⟪z, x⟫ : ℝ)} \ {x | cosR < (⟪z, x⟫ : ℝ)}
        = {x | (⟪z, x⟫ : ℝ) = cosR} := by
      ext x; simp only [Set.mem_sdiff, Set.mem_setOf_eq, not_lt]
      exact ⟨fun ⟨h1, h2⟩ => le_antisymm h2 h1, fun h => ⟨h.ge, h.le⟩⟩
    have hstrict_eq : ρ {x | cosR < (⟪z, x⟫ : ℝ)} = ρ {x | cosR ≤ (⟪z, x⟫ : ℝ)} := by
      refine le_antisymm (measure_mono hsub_cap) ?_
      calc ρ {x | cosR ≤ (⟪z, x⟫ : ℝ)}
          = ρ ({x | cosR < (⟪z, x⟫ : ℝ)} ∪
              ({x | cosR ≤ (⟪z, x⟫ : ℝ)} \ {x | cosR < (⟪z, x⟫ : ℝ)})) := by
            rw [Set.union_sdiff_cancel hsub_cap]
        _ ≤ ρ {x | cosR < (⟪z, x⟫ : ℝ)}
              + ρ ({x | cosR ≤ (⟪z, x⟫ : ℝ)} \ {x | cosR < (⟪z, x⟫ : ℝ)}) := measure_union_le _ _
        _ = ρ {x | cosR < (⟪z, x⟫ : ℝ)} := by rw [hdiff, hρlat, add_zero]
    -- closed cap ∩ 𝕊 = closed ball ∩ 𝕊
    have hset : {x | cosR ≤ (⟪z, x⟫ : ℝ)} ∩ sphere d = closedBall z r ∩ sphere d := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Metric.mem_closedBall, dist_eq_norm,
        and_congr_left_iff]
      intro hxs
      have hxnorm : ‖x‖ = 1 := norm_eq_one_of_mem_sphere hxs
      have hpol : ‖x - z‖ ^ 2 = 2 - 2 * (⟪z, x⟫ : ℝ) := by
        rw [norm_sub_sq_real, hxnorm, hznorm, real_inner_comm]; ring
      constructor
      · intro hc
        have : ‖x - z‖ ^ 2 ≤ r ^ 2 := by rw [hpol, hr2]; nlinarith
        nlinarith [norm_nonneg (x - z), Real.sq_sqrt h2c]
      · intro hd
        have : ‖x - z‖ ^ 2 ≤ r ^ 2 := by nlinarith [norm_nonneg (x - z)]
        rw [hpol, hr2] at this; nlinarith
    calc ρ {x | cosR < (⟪z, x⟫ : ℝ)}
        = ρ {x | cosR ≤ (⟪z, x⟫ : ℝ)} := hstrict_eq
      _ = ρ ({x | cosR ≤ (⟪z, x⟫ : ℝ)} ∩ sphere d) := hAS _
      _ = ρ (closedBall z r ∩ sphere d) := by rw [hset]
      _ = ρ (closedBall z r) := (hAS _).symm
  -- assemble
  refine ⟨z, cosR, hzS, hcosR_half, hcosR1, ?_, ?_⟩
  · -- cap ∩ 𝕊 ⊆ U
    intro x hxs hxcap
    apply hUball
    rw [Metric.mem_ball, dist_eq_norm]
    have hxnorm : ‖x‖ = 1 := norm_eq_one_of_mem_sphere hxs
    have hpol : ‖x - z‖ ^ 2 = 2 - 2 * (⟪z, x⟫ : ℝ) := by
      rw [norm_sub_sq_real, hxnorm, hznorm, real_inner_comm]; ring
    have hlt : ‖x - z‖ ^ 2 < r ^ 2 := by rw [hpol, hr2]; nlinarith
    have := abs_lt_of_sq_lt_sq (hlt.trans_le (by nlinarith [hr_rU] : r ^ 2 ≤ rU ^ 2)) hrU0.le
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  · -- the cap mass gap
    rw [hcapball μ hμs hlatμ, hcapball ν hνs hlatν]
    exact hgap

end MeasureToMeasure.Leaves
