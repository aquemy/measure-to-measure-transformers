import MeasureToMeasure.Leaves.SharpeningRateCompare
import MeasureToMeasure.Leaves.TaylorRemainderBound
import MeasureToMeasure.Foundations.Sphere
import MeasureToMeasure.Statements.SupportedIn
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms

/-!
# A shared-boundary point that is simultaneously non-degenerate for both measures

`phase4_atomless_nondegeneracy`, group G2. Re-scopes the earlier (refuted) attempt at this leaf
with an explicit `[NoAtoms μ0]` hypothesis: a two-atom antipodal counterexample killed the
atom-agnostic version, since an atomic `μ0` can concentrate its entire mass on exactly the two
"forbidden" points `{w, -w}` this leaf needs to avoid.

With `NoAtoms μ0`, that failure mode is impossible: `{w, -w}` is finite, hence `μ0`-null
(`Set.Finite.measure_zero`), so `μ0.support` (which carries full `μ0`-mass,
`Measure.measure_compl_support`) cannot be a subset of `{w, -w}`. This produces a witness
`x0 ∈ μ0.support \ {w, -w}`.

`w := ‖barycenter μ0‖⁻¹ • barycenter μ0` is exactly the point where Cauchy-Schwarz
(`⟪barycenter μ0, x0⟫ ≤ ‖barycenter μ0‖ * ‖x0‖`, equality iff `x0 = w`) and the tangential
projector's vanishing locus (`tangentialProjector x0 v = 0` iff `x0` and `v` are parallel unit
vectors, i.e. `x0 = ±v/‖v‖`) both degenerate. Since `barycenter μ0` and `barycenter ν0` are
forced parallel by `hcol` (colinear barycenters), both degenerate exactly at `x0 ∈ {w, -w}` -- so
avoiding that two-point set simultaneously kills all three degeneracies.

`exists_Tstar_margin_pos` builds on that witness `x0` (consuming its full 4-conjunct hypothesis,
correcting the earlier sketch's omission of the two `tangentialProjector`-nonzero conjuncts): it
runs the `pAlign` block (`TaylorRemainderBound.lean`) independently on `μ0` and `ν0` from the same
`x0` and shows the two trajectories genuinely diverge by time `τ0 := min T (κ/12)`, where
`κ := (1 - γ1) * ‖tangentialProjector x0 (barycenter ν0)‖ > 0` is the leading-order rate gap
(`colinear_tangentialProjector_eq` gives `tangentialProjector x0 (barycenter μ0) = γ1 •
tangentialProjector x0 (barycenter ν0)`, so the two fields at `x0` differ by exactly `(γ1 - 1) •
tangentialProjector x0 (barycenter ν0)`, nonzero since `γ1 < 1` and the projector is nonzero).
Combining `norm_taylor_remainder_le`'s uniform `O(τ²)` remainder for both flows with the triangle
inequality turns this `O(τ)` linear gap into a genuine positive margin `‖Φμ τ0 x0 - Φν τ0 x0‖ ≥
τ0 κ / 2 > 0` for `τ0` small enough (`≤ κ/12` keeps the combined `6τ0²` error below half the
linear term).
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Set
open MeasureToMeasure.Statements MeasureToMeasure.Foundations
open scoped RealInnerProductSpace

variable {d : ℕ}

/-- **A shared boundary point, simultaneously non-degenerate for both measures.** Given
`[NoAtoms μ0]`, colinear barycenters (`hcol`, with `γ1 ∈ (0,1)` and `barycenter ν0 ≠ 0`), there is
a point `x0` in `μ0`'s topological support that is strictly inside the Cauchy-Schwarz bound
against `barycenter μ0` (not the extremal boundary point `w`), and at which the tangential
projector of BOTH barycenters is nonzero (not parallel to `x0`). -/
theorem exists_shared_boundary_point_nondegenerate {μ0 ν0 : Measure (Eucl d)}
    [IsProbabilityMeasure μ0] [IsProbabilityMeasure ν0] [NoAtoms μ0]
    (hμs : supportedIn μ0 (sphere d)) (_hνs : supportedIn ν0 (sphere d))
    {γ1 : ℝ} (hγ1 : γ1 ∈ Set.Ioo (0:ℝ) 1)
    (hcol : barycenter μ0 = γ1 • barycenter ν0) (hνnz : barycenter ν0 ≠ 0) :
    ∃ x0 : Eucl d, x0 ∈ μ0.support ∧ ⟪barycenter μ0, x0⟫ < ‖barycenter μ0‖ ∧
      tangentialProjector x0 (barycenter ν0) ≠ 0 ∧ tangentialProjector x0 (barycenter μ0) ≠ 0 := by
  have hγ1ne : γ1 ≠ 0 := ne_of_gt hγ1.1
  have hbmu0 : barycenter μ0 ≠ 0 := by
    rw [hcol]; exact smul_ne_zero hγ1ne hνnz
  set a := barycenter μ0 with ha
  set w : Eucl d := ‖a‖⁻¹ • a with hw
  have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr hbmu0
  have hnw : ‖w‖ = 1 := norm_smul_inv_norm hbmu0
  have hsupp_sub : μ0.support ⊆ sphere d :=
    Measure.support_subset_of_isClosed Metric.isClosed_sphere hμs
  -- `μ0.support` cannot sit inside the finite (hence `μ0`-null) set `{w, -w}`.
  have hns : ¬ μ0.support ⊆ ({w, -w} : Set (Eucl d)) := by
    intro hsub
    have hfin : ({w, -w} : Set (Eucl d)).Finite := (Set.finite_singleton (-w)).insert w
    have h1 : μ0 μ0.support ≤ μ0 ({w, -w} : Set (Eucl d)) := measure_mono hsub
    have h2 : μ0 ({w, -w} : Set (Eucl d)) = 0 := hfin.measure_zero μ0
    have h3 : μ0 μ0.support = 0 := le_antisymm (h2 ▸ h1) bot_le
    have h4 : μ0 μ0.supportᶜ = 0 := Measure.measure_compl_support
    have h5 : μ0 Set.univ = 0 := by
      have hu : μ0 Set.univ ≤ μ0 μ0.support + μ0 μ0.supportᶜ := by
        rw [← Set.union_compl_self μ0.support]
        exact measure_union_le _ _
      rw [h3, h4, add_zero] at hu
      exact le_antisymm hu bot_le
    have hcontra : μ0 Set.univ ≠ 0 := by rw [measure_univ]; exact one_ne_zero
    exact hcontra h5
  obtain ⟨x0, hx0supp, hx0notin⟩ := Set.not_subset.mp hns
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx0notin
  obtain ⟨hx0w, hx0negw⟩ := hx0notin
  have hx0sphere : x0 ∈ sphere d := hsupp_sub hx0supp
  have hnx0 : ‖x0‖ = 1 := norm_eq_one_of_mem_sphere hx0sphere
  -- `tangentialProjector x0 w ≠ 0`: the vanishing locus of `P_{x0}` at `w` is exactly `x0 = ±w`.
  have hTPw : tangentialProjector x0 w ≠ 0 := by
    intro hz0
    rw [tangentialProjector_apply, sub_eq_zero] at hz0
    have hnorm : ‖w‖ = |⟪x0, w⟫| * ‖x0‖ := by
      conv_lhs => rw [hz0]
      rw [norm_smul, Real.norm_eq_abs]
    rw [hnx0, mul_one, hnw] at hnorm
    have habs : |⟪x0, w⟫| = 1 := hnorm.symm
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp habs with hc | hc
    · have : w = x0 := by rw [hz0, hc, one_smul]
      exact hx0w this.symm
    · have hweq : w = -x0 := by rw [hz0, hc, neg_one_smul]
      have : x0 = -w := by rw [hweq]; simp
      exact hx0negw this
  refine ⟨x0, hx0supp, ?_, ?_, ?_⟩
  · -- strict Cauchy-Schwarz: equality forces `x0 = w`, excluded.
    have hle : ⟪a, x0⟫ ≤ ‖a‖ * ‖x0‖ := real_inner_le_norm a x0
    rw [hnx0, mul_one] at hle
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      have heq : ‖x0‖ • a = ‖a‖ • x0 := inner_eq_norm_mul_iff_real.mp (by rw [hnx0, mul_one]; exact h)
      rw [hnx0, one_smul] at heq
      apply hx0w
      rw [hw]
      exact (eq_inv_smul_iff₀ hna).mpr heq.symm
  · -- `barycenter ν0` is a positive multiple of `w`, so its projector shares `w`'s nonvanishing.
    have hνrel : barycenter ν0 = (γ1⁻¹ * ‖a‖) • w := by
      rw [hw, smul_smul]
      have hν' : barycenter ν0 = γ1⁻¹ • a := by
        rw [hcol, smul_smul, inv_mul_cancel₀ hγ1ne, one_smul]
      rw [hν']
      congr 1
      field_simp
    rw [hνrel, tangentialProjector_smul]
    exact smul_ne_zero (mul_ne_zero (inv_ne_zero hγ1ne) hna) hTPw
  · -- `barycenter μ0`'s projector is `γ1` times `barycenter ν0`'s (`colinear_tangentialProjector_eq`).
    rw [colinear_tangentialProjector_eq hcol]
    have hνrel : barycenter ν0 = (γ1⁻¹ * ‖a‖) • w := by
      rw [hw, smul_smul]
      have hν' : barycenter ν0 = γ1⁻¹ • a := by
        rw [hcol, smul_smul, inv_mul_cancel₀ hγ1ne, one_smul]
      rw [hν']
      congr 1
      field_simp
    have hne : tangentialProjector x0 (barycenter ν0) ≠ 0 := by
      rw [hνrel, tangentialProjector_smul]
      exact smul_ne_zero (mul_ne_zero (inv_ne_zero hγ1ne) hna) hTPw
    exact smul_ne_zero hγ1ne hne

/-- **A strictly positive first-order divergence margin.** Running the same `pAlign` block
independently on `μ0` and `ν0` from the shared non-degenerate boundary point `x0`
(`exists_shared_boundary_point_nondegenerate`), the two trajectories genuinely separate by some
time `τ ∈ (0, T]`: the `O(τ)` linear rate gap forced by `γ1 < 1` and colinear barycenters
dominates the `O(τ²)` Taylor remainder for `τ` small enough. -/
theorem exists_Tstar_margin_pos {T : ℝ} (hT : 0 < T)
    {μ0 ν0 : Measure (Eucl d)} [IsProbabilityMeasure μ0] [IsProbabilityMeasure ν0] [NoAtoms μ0]
    (hμs : supportedIn μ0 (sphere d)) (hνs : supportedIn ν0 (sphere d))
    (hμint : Integrable (fun x : Eucl d => x) μ0) (hνint : Integrable (fun x : Eucl d => x) ν0)
    {γ1 : ℝ} (hγ1 : γ1 ∈ Set.Ioo (0:ℝ) 1)
    (hcol : barycenter μ0 = γ1 • barycenter ν0) (hνnz : barycenter ν0 ≠ 0)
    {Φμ Φν : ℝ → Eucl d → Eucl d}
    (hΦμ : IsMeanFieldFlow (pAlign T hT.le) μ0 Φμ) (hΦν : IsMeanFieldFlow (pAlign T hT.le) ν0 Φν) :
    ∃ x0 : Eucl d, x0 ∈ μ0.support ∧ ∃ τ ∈ Set.Ioc (0:ℝ) T, 0 < ‖Φμ τ x0 - Φν τ x0‖ := by
  obtain ⟨x0, hx0supp, _, hPν0, hPμ0⟩ :=
    exists_shared_boundary_point_nondegenerate hμs hνs hγ1 hcol hνnz
  have hx0sphere : x0 ∈ sphere d :=
    Measure.support_subset_of_isClosed Metric.isClosed_sphere hμs hx0supp
  set Pμ := tangentialProjector x0 (barycenter μ0) with hPμdef
  set Pν := tangentialProjector x0 (barycenter ν0) with hPνdef
  have hPμeq : Pμ = γ1 • Pν := colinear_tangentialProjector_eq hcol x0
  have hγ1lt1 : γ1 < 1 := hγ1.2
  -- `κ` is the leading-order (`O(τ)`) rate gap between the two flows at `x0`.
  set κ : ℝ := (1 - γ1) * ‖Pν‖ with hκdef
  have hκpos : 0 < κ := by
    apply mul_pos
    · linarith
    · exact norm_pos_iff.mpr hPν0
  set τ0 : ℝ := min T (κ / 12) with hτ0def
  have hτ0pos : 0 < τ0 := lt_min hT (by linarith)
  have hτ0leT : τ0 ≤ T := min_le_left _ _
  have hτ0leκ12 : τ0 ≤ κ / 12 := min_le_right _ _
  refine ⟨x0, hx0supp, τ0, ⟨hτ0pos, hτ0leT⟩, ?_⟩
  have hτ0Icc : τ0 ∈ Set.Icc (0:ℝ) T := ⟨hτ0pos.le, hτ0leT⟩
  have h1 := norm_taylor_remainder_le T hT.le μ0 hμs hμint Φμ hΦμ x0 hx0sphere hτ0Icc
  have h2 := norm_taylor_remainder_le T hT.le ν0 hνs hνint Φν hΦν x0 hx0sphere hτ0Icc
  -- The combined `O(τ²)` remainder for the DIFFERENCE of the two flows.
  have hdiffbound : ‖(Φμ τ0 x0 - Φν τ0 x0) - τ0 • (Pμ - Pν)‖ ≤ 6 * τ0 ^ 2 := by
    have heq : (Φμ τ0 x0 - Φν τ0 x0) - τ0 • (Pμ - Pν)
        = (Φμ τ0 x0 - x0 - τ0 • Pμ) - (Φν τ0 x0 - x0 - τ0 • Pν) := by
      rw [smul_sub]; abel
    rw [heq]
    calc ‖(Φμ τ0 x0 - x0 - τ0 • Pμ) - (Φν τ0 x0 - x0 - τ0 • Pν)‖
        ≤ ‖Φμ τ0 x0 - x0 - τ0 • Pμ‖ + ‖Φν τ0 x0 - x0 - τ0 • Pν‖ := norm_sub_le _ _
      _ ≤ 3 * τ0 ^ 2 + 3 * τ0 ^ 2 := add_le_add h1 h2
      _ = 6 * τ0 ^ 2 := by ring
  -- Reverse triangle inequality: the linear term's norm minus the remainder lower-bounds the gap.
  have hlower : ‖τ0 • (Pμ - Pν)‖ - ‖(Φμ τ0 x0 - Φν τ0 x0) - τ0 • (Pμ - Pν)‖
      ≤ ‖Φμ τ0 x0 - Φν τ0 x0‖ := by
    have hh := norm_sub_norm_le (τ0 • (Pμ - Pν)) ((τ0 • (Pμ - Pν)) - (Φμ τ0 x0 - Φν τ0 x0))
    have heq2 : (τ0 • (Pμ - Pν)) - ((τ0 • (Pμ - Pν)) - (Φμ τ0 x0 - Φν τ0 x0))
        = Φμ τ0 x0 - Φν τ0 x0 := by abel
    rw [heq2] at hh
    have heq3 : ‖(τ0 • (Pμ - Pν)) - (Φμ τ0 x0 - Φν τ0 x0)‖
        = ‖(Φμ τ0 x0 - Φν τ0 x0) - τ0 • (Pμ - Pν)‖ := norm_sub_rev _ _
    rw [heq3] at hh
    linarith
  have hPμνnorm : ‖Pμ - Pν‖ = κ := by
    rw [hPμeq]
    have heqn : γ1 • Pν - Pν = (γ1 - 1) • Pν := by rw [sub_smul, one_smul]
    rw [heqn, norm_smul, Real.norm_eq_abs]
    rw [hκdef]
    congr 1
    rw [abs_of_neg (by linarith : γ1 - 1 < 0)]
    ring
  have hτPμν : ‖τ0 • (Pμ - Pν)‖ = τ0 * κ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ0pos, hPμνnorm]
  have hfinal : τ0 * κ - 6 * τ0 ^ 2 ≤ ‖Φμ τ0 x0 - Φν τ0 x0‖ := by
    rw [← hτPμν]
    linarith [hdiffbound, hlower]
  have hpos : 0 < τ0 * κ - 6 * τ0 ^ 2 := by
    have h6 : 6 * τ0 ≤ κ / 2 := by linarith [hτ0leκ12]
    nlinarith [hτ0pos, hκpos]
  linarith [hfinal, hpos]

end MeasureToMeasure.Leaves
