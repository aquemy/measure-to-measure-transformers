import MeasureToMeasure.Leaves.OrthantBoundaryGap

/-!
# An extremal boundary point with the double-sided gap (Lemma 3.4 Part 2 leaf 5)

Leaves 1 and 3 found SOME boundary point `x0 ∈ supp μ0` with the quantitative Cauchy-Schwarz gap
`‖v‖ - ⟪v,x0⟫²/‖v‖ > 0` (`v := barycenter μ0`), via a measure-positivity argument. That argument
does not pin down `x0` to be EXTREMAL in `supp μ0` -- and extremality (specifically, `x0` minimizing
`⟪v,·⟫` over `supp μ0`) is exactly what the "local-to-global" step of the paper's App. B.3 Phase 1
argument needs: promoting leaf 4's single-point divergence into a statement about ALL of `supp μ0`.

This leaf shows the EXTREMAL point (via compactness: `supp μ0` is a closed subset of the compact
sphere, so `x ↦ ⟪v,x⟫` attains its minimum) ALSO has the double-sided gap, via a SIMPLER argument
than leaves 1/3's: the minimizer trivially satisfies `⟪v,x0⟫ ≤ ‖v‖` (Cauchy-Schwarz, everywhere on
the sphere); if this were an EQUALITY, monotonicity of the minimum would force `⟪v,x⟫ = ‖v‖` for
EVERY `x ∈ supp μ0`, hence `μ0`-a.e. (`Measure.support_mem_ae`), giving `‖v‖² = ⟪v,v⟫ = ‖v‖`,
i.e. `‖v‖ = 1` -- contradicting the strict `‖v‖ < 1` the colinearity hypothesis forces (leaf 1). So
the extremal point has `⟪v,x0⟫ < ‖v‖` strictly; the other side of the gap is the SAME orthant
argument as leaf 3.

M3b/mid-level staging: consumed when `lemma_3_4_part2` is discharged; see `Statements/MidLevel.lean`.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Set
open scoped RealInnerProductSpace
open MeasureToMeasure.Statements

variable {d : ℕ}

theorem support_subset_sphere {μ0 : Measure (Eucl d)} (hμs : μ0 (sphere d)ᶜ = 0) :
    μ0.support ⊆ sphere d := by
  have hopen : IsOpen (sphere d)ᶜ := Metric.isClosed_sphere.isOpen_compl
  have := Measure.subset_compl_support_of_isOpen hopen hμs
  rwa [compl_subset_comm, compl_compl] at this

theorem isCompact_support {μ0 : Measure (Eucl d)} (hμs : μ0 (sphere d)ᶜ = 0) :
    IsCompact μ0.support :=
  (isCompact_sphere (0 : Eucl d) 1).of_isClosed_subset Measure.isClosed_support
    (support_subset_sphere hμs)

theorem nonempty_support {μ0 : Measure (Eucl d)} [IsProbabilityMeasure μ0] :
    μ0.support.Nonempty :=
  MeasureTheory.Measure.nonempty_support (IsProbabilityMeasure.ne_zero μ0)

/-- **The extremal boundary point.** Minimizes `⟪barycenter μ0, ·⟫` over `supp μ0` (exists by
compactness), lies on the sphere, and carries the SAME quantitative Cauchy-Schwarz gap as leaves
1+3's point -- but this one is additionally KNOWN EXTREMAL, which the local-to-global argument
needs. -/
theorem exists_extremal_support_point {μ0 : Measure (Eucl d)} [IsProbabilityMeasure μ0]
    (hμs : μ0 (sphere d)ᶜ = 0) (hμint : Integrable (fun x : Eucl d => x) μ0)
    (hμorth : μ0 (orthant d)ᶜ = 0) (hvlt : ‖barycenter μ0‖ < 1) :
    ∃ x0 ∈ μ0.support, x0 ∈ sphere d ∧
      (∀ x ∈ μ0.support, ⟪barycenter μ0, x0⟫ ≤ ⟪barycenter μ0, x⟫) ∧
      0 < ‖barycenter μ0‖ - ⟪barycenter μ0, x0⟫ ^ 2 / ‖barycenter μ0‖ := by
  have hvpos : 0 < ‖barycenter μ0‖ := norm_barycenter_pos_of_orthant hμs hμint hμorth
  have hcont : ContinuousOn (fun x : Eucl d => ⟪barycenter μ0, x⟫) μ0.support :=
    (continuous_const.inner continuous_id).continuousOn
  obtain ⟨x0, hx0supp, hmin⟩ :=
    (isCompact_support hμs).exists_isMinOn nonempty_support hcont
  have hsub : μ0.support ⊆ sphere d := support_subset_sphere hμs
  have hx0sphere : x0 ∈ sphere d := hsub hx0supp
  refine ⟨x0, hx0supp, hx0sphere, hmin, ?_⟩
  set v := barycenter μ0 with hvdef
  have hcs : ∀ x ∈ sphere d, ⟪v, x⟫ ≤ ‖v‖ := by
    intro x hx
    have hb := abs_real_inner_le_norm v x
    rw [norm_eq_one_of_mem_sphere hx, mul_one] at hb
    rw [abs_le] at hb
    exact hb.2
  have hx0lt : ⟪v, x0⟫ < ‖v‖ := by
    rcases lt_or_eq_of_le (hcs x0 hx0sphere) with h | heq0
    · exact h
    · exfalso
      have hall : ∀ x ∈ μ0.support, ⟪v, x⟫ = ‖v‖ :=
        fun x hx => le_antisymm (hcs x (hsub hx)) (heq0 ▸ hmin hx)
      have hae : ∀ᵐ x ∂μ0, ⟪v, x⟫ = ‖v‖ := by
        filter_upwards [Measure.support_mem_ae (μ := μ0)] with x hx using hall x hx
      have hint2 : Integrable (fun x : Eucl d => ⟪v, x⟫) μ0 := by
        simpa using (innerSL ℝ v).integrable_comp hμint
      have heqint : ∫ x, ⟪v, x⟫ ∂μ0 = ‖v‖ := by
        rw [integral_congr_ae hae, integral_const]
        simp
      have heqv : ⟪v, v⟫ = ‖v‖ := by
        rw [← heqint, hvdef, barycenter]
        exact ((innerSL ℝ v).integral_comp_comm hμint).symm
      rw [real_inner_self_eq_norm_sq] at heqv
      nlinarith [hvpos]
  have hge : 0 ≤ ⟪v, x0⟫ := inner_nonneg_of_orthant (barycenter_mem_orthant hμs hμint hμorth)
    (support_subset_closedOrthant hμorth hx0supp)
  have hsq : ⟪v, x0⟫ ^ 2 < ‖v‖ ^ 2 := sq_lt_sq' (by linarith) hx0lt
  have hgap : ⟪v, x0⟫ ^ 2 / ‖v‖ < ‖v‖ := by
    rw [div_lt_iff₀ hvpos]
    calc ⟪v, x0⟫ ^ 2 < ‖v‖ ^ 2 := hsq
      _ = ‖v‖ * ‖v‖ := sq ‖v‖
  linarith

end MeasureToMeasure.Leaves
