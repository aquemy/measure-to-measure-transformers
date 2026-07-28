import MeasureToMeasure.Leaves.StaticAsymmetricCap
import MeasureToMeasure.Leaves.AsymmetricCapCollapse
import MeasureToMeasure.Leaves.DisentangleInductionStep
import MeasureToMeasure.Leaves.DistinctDim

/-!
# The static-cap re-based pair lemma and resolving insertion step

`exists_phase23_nonColinear_asym` (the pair lemma) and
`disentangle_insert_colinear_resolving_asym` (the insertion step consuming it).

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
open MeasureToMeasure.Foundations (isProbabilityMeasure_attnMeasureFlow
  attnMeasureFlow_supportedIn_sphere attnMeasureFlow_exists_map attnMeasureFlow_append)
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

/-- **The static-cap re-based pair-RESOLVING colinear insertion step.** The un-gated, INVOCABLE
replacement for `disentangle_insert_colinear_resolving` (`DisentangleInductionStep.lean`), whose
`hgen : GenRestNearBall d` gate is kernel-refuted (`genRestNearBall_false`, finding F22). The
conclusion is byte-identical to the gated original, so the induction over `N` consumes this step
unchanged; only the hypothesis interface moves from the refuted dynamic gate to the static-cap
route of `exists_phase23_nonColinear_asym`.

**What changed against the gated original.**
* `hgen` is DROPPED: the asymmetric collapse needs no non-degeneracy gate.
* `hout` (every bystander supported in `Uᶜ`) is REPLACED by the closed carrier `K` with
  `hKbys`/`hkK` (every bystander's support, and the `k`-side's support, inside `K`) plus the
  exclusive-point gate `hexcl` (one `j`-support point outside `K`). Bystanders and the `k`-side
  are now fixed by CAP-AVOIDANCE instead of carrier-complement support: the pair lemma exposes a
  cap whose sphere-trace avoids `K`, so `measure_cap_null_of_trace_disjoint_support` gives them
  zero cap mass and the ρ-clause fixes them literally.
* `hne` is DROPPED: it became derivable (inside the pair lemma) from `hexcl` plus `hkK`, since a
  `j`-support point off `K ⊇` (`k`-side support) forces the two flowed measures apart.
* Role asymmetry: only the `j`-side MOVES now (it is the collapse's `A`-side, staying `U`-supported
  through the S-clause at `S := U`, whose trace condition is the `W := U` half of the exposed trace
  guarantee); the `k`-side is literally fixed (`hFk`), which simplifies the original's `hFbys`/
  `hpair` case analysis. The induction hands the orientation with `k < j` preserved: the newly
  placed member `k` is the `K`-carried side, the unplaced colinear partner `j` is the
  exclusive-point side (`j` MUST be the moved one, since moving a placed member would break
  clause 3 of the invariant, and `j` is unplaced by `hjun`).
* `hbys`, `hrest`, `hsepU` carry over verbatim (module docstring of the original for why they are
  standing hypotheses, to be established by the induction that consumes this step).

The full-application non-vacuity witness (mandatory since this theorem GUARDS the induction; a
gated sibling was invocable-never before, F22) is
`Regression/NonVacuity/DisentangleResolvingAsym.lean`. -/
theorem disentangle_insert_colinear_resolving_asym {d : ℕ} (hd : 2 ≤ d) {N k : ℕ} (hk : k < N)
    (μ₀ : Fin N → Measure (Eucl d)) (hμ : ∀ i, IsProbabilityMeasure (μ₀ i))
    (hμs : ∀ i, supportedIn (μ₀ i) (sphere d))
    (θ : AttnSchedule d) (α : Fin k → Eucl d) (r : Fin k → ℝ)
    (hinv : DisentangledPrefix d N k μ₀ θ α r)
    (j : Fin N) (hjun : k < (j : ℕ))
    (U : Set (Eucl d)) (hUopen : IsOpen U) (hUorth : U ⊆ orthant d)
    (hjU : supportedIn (attnMeasureFlow θ (μ₀ j)) U)
    (hkU : supportedIn (attnMeasureFlow θ (μ₀ ⟨k, hk⟩)) U)
    (K : Set (Eucl d)) (hK : IsClosed K)
    (hKbys : ∀ i : Fin N, i ≠ j → i ≠ ⟨k, hk⟩ →
        (attnMeasureFlow θ (μ₀ i)).support ⊆ K)
    (hkK : (attnMeasureFlow θ (μ₀ ⟨k, hk⟩)).support ⊆ K)
    (hexcl : ∃ x0, x0 ∈ (attnMeasureFlow θ (μ₀ j)).support ∧ x0 ∉ K)
    (hbys : ∀ i : Fin N, i ≠ j → i ≠ ⟨k, hk⟩ → ∀ ρ : Measure (Eucl d),
        IsProbabilityMeasure ρ → supportedIn ρ (sphere d) → supportedIn ρ U →
        ∀ c : ℝ, barycenter (attnMeasureFlow θ (μ₀ i)) ≠ c • barycenter ρ)
    (hrest : Pairwise fun i i' : Fin N => i ≠ j → i ≠ ⟨k, hk⟩ → i' ≠ j → i' ≠ ⟨k, hk⟩ →
        ∀ c : ℝ, barycenter (attnMeasureFlow θ (μ₀ i))
          ≠ c • barycenter (attnMeasureFlow θ (μ₀ i')))
    (hsepU : ∀ i : Fin k, ∀ ρ : Measure (Eucl d), IsProbabilityMeasure ρ →
        supportedIn ρ (sphere d) → supportedIn ρ U →
        r i < dist (‖barycenter ρ‖⁻¹ • barycenter ρ) (α i))
    (T : ℝ) (hT : 0 < T) :
    ∃ ψ ψ' : AttnSchedule d, AttnSchedule.durationSum (ψ ++ ψ') = T ∧
      Pairwise (fun i i' : Fin N => ∀ c : ℝ,
        barycenter (attnMeasureFlow (θ ++ ψ) (μ₀ i))
          ≠ c • barycenter (attnMeasureFlow (θ ++ ψ) (μ₀ i'))) ∧
      ∃ (ω : Eucl d) (ε : ℝ), 0 < ε ∧
        DisentangledPrefix d N (k + 1) μ₀ (θ ++ (ψ ++ ψ')) (Fin.snoc α ω) (Fin.snoc r ε) := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨hsph, horth, hball, hballdisj, -⟩ := hinv
  set kk : Fin N := ⟨k, hk⟩ with hkkdef
  have hμ'p : ∀ i, IsProbabilityMeasure (attnMeasureFlow θ (μ₀ i)) :=
    fun i => haveI := hμ i; isProbabilityMeasure_attnMeasureFlow θ (μ₀ i) (hμs i)
  haveI := hμ'p j
  haveI := hμ'p kk
  -- Step 1: the static-cap pair lemma on the θ-flowed pair (`A := j`-side, `B := k`-side).
  obtain ⟨ψ, Tf, z, cosR, hTf, hdursum, hcosR, htrace, hnc1, hnc2, hfix, hS⟩ :=
    exists_phase23_nonColinear_asym (attnMeasureFlow θ (μ₀ j)) (attnMeasureFlow θ (μ₀ kk))
      T hT (hsph j) (hsph kk) U hUopen hUorth hjU hkU K hK hkK hexcl
  -- The `k`-side and every bystander have `K`-carried supports, hence zero cap mass: fixed.
  have hcapnull : ∀ i : Fin N, (attnMeasureFlow θ (μ₀ i)).support ⊆ K →
      attnMeasureFlow θ (μ₀ i) {x | cosR < (⟪z, x⟫ : ℝ)} = 0 := fun i hiK =>
    measure_cap_null_of_trace_disjoint_support _ (hsph i)
      (fun x hx hcap hsupp => (htrace x hx hcap).2 (hiK hsupp))
  have hFk : attnMeasureFlow (θ ++ ψ) (μ₀ kk) = attnMeasureFlow θ (μ₀ kk) := by
    rw [attnMeasureFlow_append]
    exact hfix _ (hsph kk) (hcapnull kk hkK)
  have hFbys : ∀ i : Fin N, i ≠ j → i ≠ kk →
      attnMeasureFlow (θ ++ ψ) (μ₀ i) = attnMeasureFlow θ (μ₀ i) := by
    intro i hij hik
    haveI := hμ'p i
    rw [attnMeasureFlow_append]
    exact hfix _ (hsph i) (hcapnull i (hKbys i hij hik))
  have hFs : ∀ i : Fin N, supportedIn (attnMeasureFlow (θ ++ ψ) (μ₀ i)) (sphere d) := by
    intro i
    rw [attnMeasureFlow_append]
    exact attnMeasureFlow_supportedIn_sphere ψ _ (hsph i)
  have hFp : ∀ i : Fin N, IsProbabilityMeasure (attnMeasureFlow (θ ++ ψ) (μ₀ i)) := by
    intro i
    haveI := hμ i
    exact isProbabilityMeasure_attnMeasureFlow (θ ++ ψ) (μ₀ i) (hμs i)
  -- The moved member stays inside the carrier: the trace lies in `U`, so `S := U` invariates.
  have hFjU : supportedIn (attnMeasureFlow (θ ++ ψ) (μ₀ j)) U := by
    rw [attnMeasureFlow_append]
    exact hS U hUopen.measurableSet (fun x hx hcap => (htrace x hx hcap).1) _ (hsph j) hjU
  have hFkU : supportedIn (attnMeasureFlow (θ ++ ψ) (μ₀ kk)) U := by
    rw [hFk]; exact hkU
  have horthsub : ∀ ρ : Measure (Eucl d), supportedIn ρ U → supportedIn ρ (orthant d) :=
    fun ρ h => measure_mono_null (Set.compl_subset_compl.mpr hUorth) h
  have hnz : ∀ ρ : Measure (Eucl d), IsProbabilityMeasure ρ → supportedIn ρ (sphere d) →
      supportedIn ρ (orthant d) → barycenter ρ ≠ 0 := by
    intro ρ hρp hρs hρo
    haveI := hρp
    exact norm_pos_iff.mp (norm_barycenter_pos_of_orthant hρs
      (integrable_id_of_sphere_support hρs) hρo)
  have hFjnz : barycenter (attnMeasureFlow (θ ++ ψ) (μ₀ j)) ≠ 0 :=
    hnz _ (hFp j) (hFs j) (horthsub _ hFjU)
  have hFknz : barycenter (attnMeasureFlow (θ ++ ψ) (μ₀ kk)) ≠ 0 :=
    hnz _ (hFp kk) (hFs kk) (horthsub _ hFkU)
  -- Step 2: whole-family pairwise non-colinearity after `θ ++ ψ`.
  have hpair : Pairwise (fun i i' : Fin N => ∀ c : ℝ,
      barycenter (attnMeasureFlow (θ ++ ψ) (μ₀ i))
        ≠ c • barycenter (attnMeasureFlow (θ ++ ψ) (μ₀ i'))) := by
    intro a b hab
    by_cases haj : a = j
    · have hbj : b ≠ j := by rw [← haj]; exact Ne.symm hab
      by_cases hbk : b = kk
      · rw [haj, hbk]
        simpa [attnMeasureFlow_append] using hnc1
      · rw [haj, hFbys b hbj hbk]
        exact ne_smul_flip_of_ne_zero hFjnz (hbys b hbj hbk _ (hFp j) (hFs j) hFjU)
    · by_cases hak : a = kk
      · have hbk : b ≠ kk := by rw [← hak]; exact Ne.symm hab
        by_cases hbj : b = j
        · rw [hak, hbj]
          simpa [attnMeasureFlow_append] using hnc2
        · rw [hak, hFbys b hbj hbk]
          exact ne_smul_flip_of_ne_zero hFknz (hbys b hbj hbk _ (hFp kk) (hFs kk) hFkU)
      · rw [hFbys a haj hak]
        by_cases hbj : b = j
        · rw [hbj]
          exact hbys a haj hak _ (hFp j) (hFs j) hFjU
        · by_cases hbk : b = kk
          · rw [hbk]
            exact hbys a haj hak _ (hFp kk) (hFs kk) hFkU
          · rw [hFbys b hbj hbk]
            exact hrest hab haj hak hbj hbk
  -- Step 3: the prefix invariant survives.
  have hprefix : DisentangledPrefix d N k μ₀ (θ ++ ψ) α r := by
    refine ⟨hFs, ?_, ?_, hballdisj, ?_⟩
    · intro i
      by_cases hij : i = j
      · rw [hij]; exact horthsub _ hFjU
      · by_cases hik : i = kk
        · rw [hik, hFk]; exact horth kk
        · rw [hFbys i hij hik]; exact horth i
    · intro i hik
      have hij : i ≠ j := by intro h; rw [h] at hik; omega
      have hikk : i ≠ kk := by
        intro h; rw [h, hkkdef] at hik; simp at hik
      rw [hFbys i hij hikk]; exact hball i hik
    · intro i _
      haveI := hμ i
      obtain ⟨Φ, Φinv, hΦm, -, hΦinvm, hΦeq, -, hΦinv⟩ :=
        attnMeasureFlow_exists_map (θ ++ ψ) (μ₀ i) (hμs i)
      exact ⟨Φ, Φinv, hΦm, hΦinvm, hΦeq, hΦinv⟩
  have hsep : ∀ i : Fin k, r i < dist
      (‖barycenter (attnMeasureFlow (θ ++ ψ) (μ₀ ⟨k, hk⟩))‖⁻¹ •
        barycenter (attnMeasureFlow (θ ++ ψ) (μ₀ ⟨k, hk⟩))) (α i) :=
    fun i => hsepU i _ (hFp kk) (hFs kk) hFkU
  -- Step 4: the banked non-colinear insertion on the composed schedule.
  obtain ⟨ψ', hdur', ω, ε, hεpos, hprefix'⟩ :=
    disentangle_insert_noncolinear hk μ₀ hμ hμs (θ ++ ψ) α r hprefix hpair hsep Tf hTf
  refine ⟨ψ, ψ', ?_, hpair, ω, ε, hεpos, ?_⟩
  · simp only [AttnSchedule.durationSum_append, hdur']
    exact hdursum
  · rw [← List.append_assoc]
    exact hprefix'

end MeasureToMeasure.Leaves
