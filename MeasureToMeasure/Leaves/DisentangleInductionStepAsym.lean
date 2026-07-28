import MeasureToMeasure.Leaves.StaticAsymmetricCap
import MeasureToMeasure.Leaves.AsymmetricCapCollapse
import MeasureToMeasure.Leaves.DisentangleInductionStep
import MeasureToMeasure.Leaves.DistinctDim

/-!
# The static-cap re-based pair lemma: `exists_phase23_nonColinear_asym`

The un-gated replacement for `exists_phase23_nonColinear` (and, through its two-directional
conclusion, for `exists_phase3_nonColinear_symm`), both in `DisentangleInductionStep.lean`. Those
originals are kernel-clean but NOT invocable: they thread `hgen : GenRestNearBall d`, which
`Regression/Refuted/HgenRestUnconditionallyFalse.lean` refutes in the kernel
(`genRestNearBall_false`, finding F22). They are kept untouched as documented history of the
Phase-2/Phase-3 architecture; this file is the live route.

## Why `hne` and `hcol` are absent

The gated originals ran Phase 2 (`barycenter_ne_of_massGapCollapse_meanField`, needing
`hne : μ ≠ ν`) to separate the barycenters, then Phase 3 (gated) to break the residual colinearity
`barycenter μ = γ • barycenter ν` recorded by `hcol`, with delicate `γ`-bookkeeping in between. The
asymmetric collapse (`exists_asymmetric_collapse_schedule`) is UNCONDITIONAL in both respects: given
any cap with positive `A`-mass and zero `B`-mass, its single block defeats EVERY scalar `γ₂` at
once, including `γ₂ = 1` (barycenter equality) and the colinear range `γ₂ ∈ (0, 1)`, while fixing
the `B`-side literally. So there is no Phase 2, no case split on a residual `γ`, and no
distinctness or colinearity hypothesis: the whole `hne`/`hcol` interface disappears. (`A ≠ B` is
still TRUE here, derived from the gate below, but only to recover `2 ≤ d` via
`two_le_d_of_distinct`, never as a separation input.)

## The gate: an exclusive support point against a closed carrier `K`

What replaces the refuted dynamic gate is pure static point-set topology: a closed set `K` carrying
the whole `B`-support (`hBK : B.support ⊆ K`), and one `A`-support point outside `K` (`hexcl`).
`exists_static_cap_in_open_avoiding_closed` then places a cap `{cosR < ⟪z, ·⟫}` with positive
`A`-mass whose sphere-trace stays inside the open carrier `W` and clear of `K`;
`measure_cap_null_of_trace_disjoint_support` converts trace-avoidance of `K ⊇ B.support` into
`B`-nullity of the cap. In the induction over `N`, `K` is chosen to carry the `B`-side AND every
bystander, so the single exposed cap simultaneously certifies (through the two bystander conjuncts)
that all of them are fixed.

## Interface change for the caller: cap-avoidance instead of `Uᶜ`-fixing

The gated originals fixed bystanders supported in `Uᶜ` and preserved regions `S ⊇ U`. Here the cap
`(z, cosR)` is EXPOSED in the conclusion together with its trace guarantee
(`∀ x ∈ sphere d, cosR < ⟪z, x⟫ → x ∈ W ∧ x ∉ K`), and the two bystander conjuncts are stated
against the cap: any sphere probability measure with ZERO CAP MASS is fixed literally, and any
measurable `S` containing the cap's sphere-trace forward-invariates every `S`-carried sphere
probability measure. The caller replaces the old carrier bookkeeping by cap-avoidance, e.g. reading
`ρ (cap) = 0` for a `K`-supported bystander off the same trace clause via
`measure_cap_null_of_trace_disjoint_support`, and instantiates `S := orthant d` (the trace lands in
`W ⊆ orthant d`) for orthant preservation, exactly as done for the flip inside this proof.

M3b/mid-level staging: consumed by the static-cap re-base of `exists_disentangling_balls`'s
induction over `N`; see the `exists-disentangling-balls-campaign` notes.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Set MeasureToMeasure MeasureToMeasure.Statements
open MeasureToMeasure.Foundations (AttnSchedule AttnParams attnMeasureFlow)
open scoped RealInnerProductSpace

/-- **The static-cap pair lemma: `A` made non-colinear with `B` in both directions, `B` and all
cap-avoiding bystanders literally fixed.** Given sphere-supported probability measures `A`, `B`
carried by an open `W ⊆ orthant d`, a closed `K` carrying `B`'s support, and one `A`-support point
outside `K`, some schedule `ψ` (a single asymmetric-collapse block of duration `T / 2`, leaving the
strictly positive remainder `Tf = T / 2` to the caller) makes the flowed barycenters non-colinear
for EVERY scalar in BOTH directions, while exposing the static cap `(z, cosR)` it used: the cap's
sphere-trace lies in `W` and avoids `K`, every sphere probability measure with zero cap mass
(in particular `B` itself, and every `K`-supported bystander via
`measure_cap_null_of_trace_disjoint_support`) is fixed literally, and every measurable region
containing the cap's sphere-trace is forward-invariant.

No `hne`, no `hcol`, no `GenRestNearBall` gate: the asymmetric collapse is unconditional (see the
module docstring). Replaces the F22-gated `exists_phase23_nonColinear` /
`exists_phase3_nonColinear_symm`. The reverse non-colinearity direction is
`ne_smul_flip_of_ne_zero` applied to `barycenter B ≠ 0` (orthant support through `W ⊆ orthant d`
and `norm_barycenter_pos_of_orthant`), using that the flowed `B`-side IS `B`. `2 ≤ d` (needed by
the collapse's pole pigeonhole) is not a hypothesis: it is recovered by `two_le_d_of_distinct`
from `A ≠ B`, itself forced by the exclusive support point (`x0 ∈ A.support`, `x0 ∉ K ⊇
B.support`). -/
theorem exists_phase23_nonColinear_asym {d : ℕ} [NeZero d]
    (A B : Measure (Eucl d)) [IsProbabilityMeasure A] [IsProbabilityMeasure B]
    (T : ℝ) (hT : 0 < T)
    (hAs : supportedIn A (sphere d)) (hBs : supportedIn B (sphere d))
    (W : Set (Eucl d)) (hWopen : IsOpen W) (hWorth : W ⊆ orthant d)
    (hAW : supportedIn A W) (hBW : supportedIn B W)
    (K : Set (Eucl d)) (hK : IsClosed K) (hBK : B.support ⊆ K)
    (hexcl : ∃ x0, x0 ∈ A.support ∧ x0 ∉ K) :
    ∃ (ψ : AttnSchedule d) (Tf : ℝ) (z : Eucl d) (cosR : ℝ),
      0 < Tf ∧ AttnSchedule.durationSum ψ + Tf = T ∧
      cosR ∈ Set.Ioo (1 / 2 : ℝ) 1 ∧
      (∀ x ∈ sphere d, cosR < (⟪z, x⟫ : ℝ) → x ∈ W ∧ x ∉ K) ∧
      (∀ c : ℝ, barycenter (attnMeasureFlow ψ A) ≠ c • barycenter (attnMeasureFlow ψ B)) ∧
      (∀ c : ℝ, barycenter (attnMeasureFlow ψ B) ≠ c • barycenter (attnMeasureFlow ψ A)) ∧
      (∀ ρ : Measure (Eucl d), [IsProbabilityMeasure ρ] → supportedIn ρ (sphere d) →
        ρ {x | cosR < (⟪z, x⟫ : ℝ)} = 0 → attnMeasureFlow ψ ρ = ρ) ∧
      (∀ S : Set (Eucl d), MeasurableSet S →
        (∀ x ∈ sphere d, cosR < (⟪z, x⟫ : ℝ) → x ∈ S) →
        ∀ ρ : Measure (Eucl d), [IsProbabilityMeasure ρ] → supportedIn ρ (sphere d) →
          supportedIn ρ S → supportedIn (attnMeasureFlow ψ ρ) S) := by
  -- orthant support of both sides; `A ≠ B` since `A` has a support point off `K ⊇ B.support`
  have hAo : supportedIn A (orthant d) :=
    measure_mono_null (Set.compl_subset_compl.mpr hWorth) hAW
  have hBo : supportedIn B (orthant d) :=
    measure_mono_null (Set.compl_subset_compl.mpr hWorth) hBW
  have hAB : A ≠ B := by
    obtain ⟨x0, hx0A, hx0K⟩ := hexcl
    intro h
    exact hx0K (hBK (h ▸ hx0A))
  have hd2 : 2 ≤ d := two_le_d_of_distinct hAB hAs hBs hAo hBo
  -- the static cap: `A`-positive, sphere-trace inside `W` and clear of `K`
  obtain ⟨z, cosR, hznorm, hcosR, hAcap, htrace⟩ :=
    exists_static_cap_in_open_avoiding_closed A hAs W hWopen hAW K hK hexcl
  have hzs : z ∈ sphere d := by
    rw [sphere, Metric.mem_sphere, dist_zero_right, hznorm]
  -- the cap is `B`-null: its sphere-trace avoids `K`, which carries all of `B.support`
  have hBcap : B {x | cosR < (⟪z, x⟫ : ℝ)} = 0 :=
    measure_cap_null_of_trace_disjoint_support B hBs
      (fun x hx hcap hsupp => (htrace x hx hcap).2 (hBK hsupp))
  -- the asymmetric collapse block, at duration `T / 2`
  obtain ⟨p, hpdur, hBfix, hγ, hfix, hS⟩ :=
    exists_asymmetric_collapse_schedule hd2 A B hAs hBs hzs hcosR hAcap hBcap
      (T2 := T / 2) (by linarith)
  -- flip direction: the `B`-side barycenter is nonzero (orthant) and literally untouched
  have hBnz : barycenter B ≠ 0 :=
    norm_pos_iff.mp (norm_barycenter_pos_of_orthant hBs
      (integrable_id_of_sphere_support hBs) hBo)
  have hγ' : ∀ c : ℝ, barycenter (attnMeasureFlow [p] A) ≠ c • barycenter B := by
    intro c
    have := hγ c
    rwa [hBfix] at this
  have hflip : ∀ c : ℝ, barycenter (attnMeasureFlow [p] B)
      ≠ c • barycenter (attnMeasureFlow [p] A) := by
    rw [hBfix]
    exact ne_smul_flip_of_ne_zero hBnz hγ'
  have hdur1 : AttnSchedule.durationSum [p] = p.duration := by
    simp [AttnSchedule.durationSum]
  refine ⟨[p], T / 2, z, cosR, by linarith, ?_, hcosR, htrace, hγ, hflip, hfix, hS⟩
  rw [hdur1, hpdur]
  ring

end MeasureToMeasure.Leaves
