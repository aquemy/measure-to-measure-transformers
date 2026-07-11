import MeasureToMeasure.Leaves.GatedTwoCap
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The gated flow, localized to the starting ball's own center (lemma_B_1/B_2, union-form step 1)

`lemma_B_1`'s docstring documents a gap (review finding F16) relative to the paper's own Lemma B.1:
the Lean construction cannot yet express "the flow is the identity outside the starting ball `ℬ₀`",
because `gated_twoCap_retention` (`Leaves/GatedTwoCap.lean`) recenters its gate at the overlap point
`ω` (calling `scaledGatedBlock hωn hωn ...`, unifying the gate-center `z` with the push-direction
`ω`), not at `ℬ₀`'s own center `z₀`. This makes the field vanish outside a cap centered at `ω` --
which, when `ω` sits near `ℬ₀`'s rim, can be nearly the whole sphere -- not outside `ℬ₀` itself.

This leaf builds the localized alternative: `gatedField z₀ ω cosR` (gate centered at `z₀`, still
pushing toward `ω`). This exactly matches the paper's own Lemma B.2 construction (Appendix B,
pp. 31-32: "Let `z` denote the center... of `B₀`"), confirming the `z = ω` unification in the
existing Lean code is a deviation from the paper, not a faithful transcription.

**The reach invariant** (`scaledGatedBlock_z0_inner_ge`): the crux new fact. With the gate
localized at `z₀`, the trajectory's `z₀`-coordinate never drops below `min(⟪x,z₀⟩, ⟪ω,z₀⟩)`, for
`x, ω` both inside `ℬ₀`. The naive triangle-inequality bound `geodesicDist(z₀,·) ≤
geodesicDist(z₀,ω) + geodesicDist(ω,·)` is NOT tight enough to see this (it can legitimately exceed
`R₀` when `ω` is near the rim). The actual proof is a genuine ODE comparison argument: writing
`h(t) := ⟪Φ_t(x),z₀⟩`, its derivative (`hasDerivAt_inner_scaledFlow_other`, the same algebra as the
existing `gate_hasDerivAt_inner` but paired against `z₀` instead of the push direction `ω`) is
`h'(t) = g(t)·(⟪ω,z₀⟩ - u(t)·h(t))` where `u(t) := ⟪Φ_t(x),ω⟩`. Whenever `h(t)` touches the barrier
level `L := min(⟪x,z₀⟩,⟪ω,z₀⟩)` exactly, `h'(t) > 0` strictly (the gate is strictly positive there
since `L` is strictly inside `ℬ₀`, and `u(t) < 1` strictly since the trajectory never reaches the
fixed point `ω`, so `u(t)·L < L ≤ ⟪ω,z₀⟩`) -- so `h` can never actually cross the barrier from above.
Mathlib's `image_le_of_deriv_right_lt_deriv_boundary` packages exactly this "can't cross a barrier
where the derivative points away from crossing" comparison principle.

**The reach toward the target** (`scaledGatedBlock_z0_reach`): given the invariant, `gateFactor
z₀ cosR` is uniformly bounded below by `A·(L - cosR)` throughout the trajectory (the SAME uniform
bound the un-localized construction gets "for free" by making the gate coincide with the push
direction) -- so `logistic_flow_reach` (the same tool `scaledGatedBlock_reach` uses) gives an
explicit finite-time bound on `⟪Φ_T(x),ω⟩`.

**Identity outside the ball** (`scaledGatedBlock_z0_fixed_of_le`): cheap, as expected -- the
localized field is *exactly* zero for `⟪z₀,x⟩ ≤ cosR` (immediate from `reluGate`'s `max 0 (·)`), so
such points are fixed by `Block.blockFlow_fixed`.

M3b/mid-level staging: Step 1 of strengthening `lemma_B_1`/`lemma_B_2` to the union form needed by
`prop_2_2`'s Step 3; see `Statements/MidLevel.lean`.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Set
open scoped RealInnerProductSpace
open MeasureToMeasure

variable {d : ℕ}

/-- The gated drift `tangentialProjector x (g•ω)` paired against a direction `z₀` other than the
push direction `ω`: `⟪gatedDrift, z₀⟩ = g·(⟪ω,z₀⟩ - ⟪x,ω⟩⟪x,z₀⟩)`. Generalizes `gate_inner_identity`
(which pairs against `ω` itself) to an arbitrary tracked direction. -/
theorem gate_inner_identity_other {x ω z₀ : Eucl d} (g : ℝ) :
    ⟪tangentialProjector x (g • ω), z₀⟫ = g * (⟪ω, z₀⟫ - ⟪x, ω⟫ * ⟪x, z₀⟫) := by
  rw [tangentialProjector_apply, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_right, mul_sub]
  ring

/-- The gate ODE (B.5) for a curve driven by the gated drift, tracked against a direction `z₀`
other than the push direction `ω`. Generalizes `gate_hasDerivAt_inner`. -/
theorem gate_hasDerivAt_inner_other {x : ℝ → Eucl d} {ω z₀ : Eucl d} {t : ℝ} {x' : Eucl d}
    (hx : HasDerivAt x x' t) (g : ℝ)
    (hode : x' = tangentialProjector (x t) (g • ω)) :
    HasDerivAt (fun s => (⟪x s, z₀⟫ : ℝ)) (g * (⟪ω, z₀⟫ - ⟪x t, ω⟫ * ⟪x t, z₀⟫)) t := by
  have hconst : HasDerivAt (fun _ : ℝ => z₀) (0 : Eucl d) t := hasDerivAt_const t z₀
  have h := hx.inner ℝ hconst
  rw [hode, gate_inner_identity_other] at h
  simpa using h

/-- The gate ODE along the amplitude-scaled gated flow, gate at `z₀`, push toward `ω`, tracked
against `z₀` itself. Generalizes `hasDerivAt_inner_scaledFlow`. -/
theorem hasDerivAt_inner_scaledFlow_other {A : ℝ} {z₀ ω : Eucl d} (cosR : ℝ)
    (b : Block d) (hfield : b.field = scaledGatedField A z₀ ω cosR)
    {x : Eucl d} {t : ℝ} :
    HasDerivAt (fun s => (⟪b.blockFlow s x, z₀⟫ : ℝ))
      ((A * gateFactor z₀ cosR (b.blockFlow t x)) *
        (⟪ω, z₀⟫ - ⟪b.blockFlow t x, ω⟫ * ⟪b.blockFlow t x, z₀⟫)) t := by
  have hcurve : HasDerivAt (b.blockCurve x) (b.field (b.blockCurve x t)) t :=
    b.blockCurve_isIntegralCurve x t
  have hvel : b.field (b.blockCurve x t)
      = tangentialProjector (b.blockCurve x t)
          ((A * gateFactor z₀ cosR (b.blockCurve x t)) • ω) := by
    rw [hfield, scaledGatedField_eq_projector_smul]
  exact gate_hasDerivAt_inner_other hcurve (A * gateFactor z₀ cosR (b.blockCurve x t)) hvel

/-- **The localized-gate reach invariant, for the whole trajectory.** Transporting toward `ω` with
the gate centered at `z₀` (not `ω`), the trajectory's `z₀`-coordinate never drops below
`min(⟪x,z₀⟩, ⟪ω,z₀⟩)`, at any time in `[0,T]`. This is what lets the flow stay confined to `ℬ₀`
(`z₀`'s own ball) throughout, rather than only near the endpoint. -/
theorem scaledGatedBlock_z0_inner_ge {A : ℝ} (hA : 0 < A) {z₀ ω : Eucl d} (hz₀ : ‖z₀‖ = 1)
    (hω : ‖ω‖ = 1) {cosR : ℝ} (hcosR : 0 ≤ cosR) {T : ℝ} (hT : 0 ≤ T)
    {x : Eucl d} (hx : x ∈ sphere d) (hne : x ≠ ω) (hne' : x ≠ -ω)
    (hxcap : cosR < (⟪x, z₀⟫ : ℝ)) (hωcap : cosR < (⟪ω, z₀⟫ : ℝ)) :
    ∀ s ∈ Set.Icc (0:ℝ) T, min (⟪x, z₀⟫ : ℝ) (⟪ω, z₀⟫ : ℝ)
      ≤ (⟪(scaledGatedBlock hA.le hz₀ hω (by linarith : (-1:ℝ) ≤ cosR) hT).blockFlow s x, z₀⟫ : ℝ) := by
  have hz₀s : z₀ ∈ sphere d := by rw [sphere, Metric.mem_sphere, dist_zero_right, hz₀]
  have hωs : ω ∈ sphere d := by rw [sphere, Metric.mem_sphere, dist_zero_right, hω]
  set B := scaledGatedBlock hA.le hz₀ hω (by linarith : (-1:ℝ) ≤ cosR) hT with hBdef
  have hfield : B.field = scaledGatedField A z₀ ω cosR := rfl
  set L := min (⟪x, z₀⟫ : ℝ) (⟪ω, z₀⟫ : ℝ) with hLdef
  have hLpos : cosR < L := lt_min hxcap hωcap
  set f : ℝ → ℝ := fun t => -(⟪B.blockFlow t x, z₀⟫ : ℝ) with hfdef
  set f' : ℝ → ℝ := fun t => -((A * gateFactor z₀ cosR (B.blockFlow t x)) *
      (⟪ω, z₀⟫ - ⟪B.blockFlow t x, ω⟫ * ⟪B.blockFlow t x, z₀⟫)) with hf'def
  have hfderiv : ∀ t : ℝ, HasDerivAt f (f' t) t := by
    intro t
    exact (hasDerivAt_inner_scaledFlow_other cosR B hfield (x := x) (t := t)).neg
  have hkey : ∀ t ∈ Set.Ico (0:ℝ) T, f t = -L → f' t < 0 := by
    intro t ht_mem heq
    have hht : (⟪B.blockFlow t x, z₀⟫ : ℝ) = L := by
      rw [hfdef] at heq; simp only at heq; linarith
    have hht' : (⟪z₀, B.blockFlow t x⟫ : ℝ) = L := by rw [real_inner_comm]; exact hht
    have hsph : B.blockFlow t x ∈ sphere d :=
      B.blockFlow_mem_sphere hx (Set.mem_Ico.mp ht_mem).1
    have hgate : gateFactor z₀ cosR (B.blockFlow t x) = L - cosR := by
      rw [gateFactor_eq_reluGate_of_mem_sphere cosR hsph, reluGate, hht']
      exact max_eq_right (by linarith)
    have hg_pos : 0 < A * gateFactor z₀ cosR (B.blockFlow t x) := by
      rw [hgate]; exact mul_pos hA (by linarith)
    have hu_lt : (⟪B.blockFlow t x, ω⟫ : ℝ) < 1 :=
      (inner_scaledFlow_mem_Ioo hωs cosR B hfield hx hne hne' (Set.mem_Ico.mp ht_mem).1).2
    have hcomp_pos : 0 < (⟪ω, z₀⟫ : ℝ) - ⟪B.blockFlow t x, ω⟫ * ⟪B.blockFlow t x, z₀⟫ := by
      rw [hht]
      have h1 : (⟪B.blockFlow t x, ω⟫ : ℝ) * L < 1 * L :=
        mul_lt_mul_of_pos_right hu_lt (by linarith)
      have h2 : L ≤ (⟪ω, z₀⟫ : ℝ) := min_le_right _ _
      linarith
    rw [hf'def]
    simp only
    have := mul_pos hg_pos hcomp_pos
    linarith
  have hcont : ContinuousOn f (Set.Icc 0 T) := fun t _ => (hfderiv t).continuousAt.continuousWithinAt
  have hderivwithin : ∀ t ∈ Set.Ico (0:ℝ) T, HasDerivWithinAt f (f' t) (Set.Ici t) t :=
    fun t _ => (hfderiv t).hasDerivWithinAt
  have hstart : f 0 ≤ (fun _ : ℝ => -L) 0 := by
    have hb0 : B.blockFlow 0 x = x := B.blockFlow_zero x
    rw [hfdef]; simp only [hb0]
    have : L ≤ (⟪x, z₀⟫ : ℝ) := min_le_left _ _
    linarith
  have hBderiv : ∀ t : ℝ, HasDerivAt (fun _ : ℝ => -L) (0:ℝ) t := fun t => hasDerivAt_const t (-L)
  intro s hs
  have hbound := image_le_of_deriv_right_lt_deriv_boundary hcont hderivwithin hstart hBderiv hkey hs
  rw [hfdef] at hbound
  have : (fun t => -(⟪B.blockFlow t x, z₀⟫ : ℝ)) s ≤ (fun _ : ℝ => -L) s := hbound
  simp only at this
  linarith

/-- **Finite-time reach toward the target, with the gate localized at `z₀`.** The reach invariant
gives a uniform gate lower bound `A·(L - cosR)` throughout the trajectory (`L := min(⟪x,z₀⟩,
⟪ω,z₀⟩)`), which feeds directly into the same `logistic_flow_reach` comparison the un-localized
construction (`scaledGatedBlock_reach`) uses. -/
theorem scaledGatedBlock_z0_reach {A : ℝ} (hA : 0 < A) {z₀ ω : Eucl d} (hz₀ : ‖z₀‖ = 1)
    (hω : ‖ω‖ = 1) {cosR : ℝ} (hcosR : 0 ≤ cosR) {T : ℝ} (hT : 0 ≤ T)
    {x : Eucl d} (hx : x ∈ sphere d) (hne : x ≠ ω) (hne' : x ≠ -ω)
    (hxcap : cosR < (⟪x, z₀⟫ : ℝ)) (hωcap : cosR < (⟪ω, z₀⟫ : ℝ)) {b : ℝ} (hb : b ∈ Set.Ioo (-1:ℝ) 1)
    (hreach : logOdds b ≤ logOdds (⟪x, ω⟫ : ℝ)
      + 2 * (A * (min (⟪x, z₀⟫ : ℝ) (⟪ω, z₀⟫ : ℝ) - cosR)) * T) :
    b ≤ (⟪(scaledGatedBlock hA.le hz₀ hω (by linarith : (-1:ℝ) ≤ cosR) hT).blockFlow T x, ω⟫ : ℝ) := by
  have hz₀s : z₀ ∈ sphere d := by rw [sphere, Metric.mem_sphere, dist_zero_right, hz₀]
  have hωs : ω ∈ sphere d := by rw [sphere, Metric.mem_sphere, dist_zero_right, hω]
  set B := scaledGatedBlock hA.le hz₀ hω (by linarith : (-1:ℝ) ≤ cosR) hT with hBdef
  have hfield : B.field = scaledGatedField A z₀ ω cosR := rfl
  set L := min (⟪x, z₀⟫ : ℝ) (⟪ω, z₀⟫ : ℝ) with hLdef
  set u : ℝ → ℝ := fun s => (⟪B.blockFlow s x, ω⟫ : ℝ) with hu_def
  set g : ℝ → ℝ := fun s => A * gateFactor z₀ cosR (B.blockFlow s x) with hg_def
  have hu0 : u 0 = (⟪x, ω⟫ : ℝ) := by simp [hu_def, B.blockFlow_zero]
  have hu_ode : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt u (g t * (1 - (u t) ^ 2)) t :=
    fun t ht => hasDerivAt_inner_scaledFlow hωs cosR B hfield hx ht.1
  have hu_range : ∀ t ∈ Set.Icc (0 : ℝ) T, u t ∈ Set.Ioo (-1 : ℝ) 1 :=
    fun t ht => inner_scaledFlow_mem_Ioo hωs cosR B hfield hx hne hne' ht.1
  have hginv := scaledGatedBlock_z0_inner_ge hA hz₀ hω hcosR hT hx hne hne' hxcap hωcap
  have hg_lb : ∀ t ∈ Set.Icc (0 : ℝ) T, A * (L - cosR) ≤ g t := by
    intro t ht
    have hle : L ≤ (⟪B.blockFlow t x, z₀⟫ : ℝ) := hginv t ht
    have hle' : L ≤ (⟪z₀, B.blockFlow t x⟫ : ℝ) := by rw [real_inner_comm]; exact hle
    have hsph : B.blockFlow t x ∈ sphere d := B.blockFlow_mem_sphere hx ht.1
    have hgt : gateFactor z₀ cosR (B.blockFlow t x) = reluGate z₀ cosR (B.blockFlow t x) :=
      gateFactor_eq_reluGate_of_mem_sphere cosR hsph
    rw [hg_def]
    simp only
    rw [hgt, reluGate]
    have : L - cosR ≤ max 0 ((⟪z₀, B.blockFlow t x⟫ : ℝ) - cosR) :=
      le_max_of_le_right (by linarith)
    exact mul_le_mul_of_nonneg_left this hA.le
  exact logistic_flow_reach hT hu_ode hu_range hg_lb hb (by rw [hu0]; exact hreach)

/-- **Identity outside the gated ball.** The `z₀`-localized field is exactly zero for points with
`⟪z₀,x⟩ ≤ cosR`, so such points are fixed by the whole flow -- unlike the un-localized construction
(gate at `ω`), this holds regardless of where `ω` sits, since the gate depends only on `z₀`. -/
theorem scaledGatedBlock_z0_fixed_of_le {A : ℝ} (hA : 0 ≤ A) {z₀ ω : Eucl d} (hz₀ : ‖z₀‖ = 1)
    (hω : ‖ω‖ = 1) {cosR : ℝ} (hcosR : -1 ≤ cosR) {T : ℝ} (hT : 0 ≤ T)
    {x : Eucl d} (hle : (⟪z₀, x⟫ : ℝ) ≤ cosR) (t : ℝ) :
    (scaledGatedBlock hA hz₀ hω hcosR hT).blockFlow t x = x := by
  apply Block.blockFlow_fixed
  show scaledGatedField A z₀ ω cosR x = 0
  rw [scaledGatedField, gatedField, gateFactor, reluGate]
  rw [max_eq_left (by linarith : (⟪z₀, x⟫ : ℝ) - cosR ≤ 0), mul_zero, zero_smul, smul_zero]

/-- Choosing the amplitude `A` from the log-odds budget, the `z₀`-localized gated flow maps the
two-threshold source cap (`m` toward `ω`, `m₀` toward `z₀`) into the target cap `{b ≤ ⟪·,ω⟫}`.
The two-threshold form is what `gated_twoCap_retention_localized` needs: `m₀` keeps the source cap
inside `ℬ₀` (so the localized gate is uniformly bounded below there), `m` is the actual reach
requirement toward `ω`. Generalizes `exists_scaledGatedBlock_mapsTo_cap`. -/
theorem exists_scaledGatedBlock_z0_mapsTo_cap {z₀ ω : Eucl d} (hz₀n : ‖z₀‖ = 1) (hωn : ‖ω‖ = 1)
    {T : ℝ} (hT : 0 < T)
    {cosR₀ m₀ m b : ℝ} (hcosR₀_nonneg : 0 ≤ cosR₀)
    (hm₀cap : cosR₀ < m₀) (hωcap : cosR₀ < (⟪ω, z₀⟫ : ℝ))
    (hm_gt : (-1:ℝ) < m) (hm_lt_one : m < 1) (hb_mem : b ∈ Set.Ioo (-1:ℝ) 1)
    (hωs : ω ∈ sphere d) :
    ∃ (A : ℝ) (hA : 0 < A), Set.MapsTo
      ((scaledGatedBlock hA.le hz₀n hωn (by linarith : (-1:ℝ) ≤ cosR₀) hT.le).blockFlow T)
      {x | x ∈ sphere d ∧ m ≤ (⟪x, ω⟫ : ℝ) ∧ m₀ ≤ (⟪x, z₀⟫ : ℝ)} {y | b ≤ (⟪y, ω⟫ : ℝ)} := by
  set q := (logOdds b - logOdds m) / (2 * (min m₀ (⟪ω, z₀⟫ : ℝ) - cosR₀) * T) with hq
  have hden : 0 < 2 * (min m₀ (⟪ω, z₀⟫ : ℝ) - cosR₀) * T := by
    have : 0 < min m₀ (⟪ω, z₀⟫ : ℝ) - cosR₀ := by rw [sub_pos]; exact lt_min hm₀cap hωcap
    positivity
  refine ⟨max 1 q, lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro x hx
  obtain ⟨hxs, hxm, hxm₀⟩ := hx
  by_cases hxω : x = ω
  · have hfix : (scaledGatedBlock (le_of_lt (lt_of_lt_of_le one_pos (le_max_left 1 q))) hz₀n hωn
        (by linarith : (-1:ℝ) ≤ cosR₀) hT.le).blockFlow T ω = ω :=
      Block.blockFlow_fixed _ (by
        show scaledGatedField (max 1 q) z₀ ω cosR₀ ω = 0
        rw [scaledGatedField, gatedField_pole_eq_zero hωs, smul_zero]) T
    show b ≤ (⟪_, ω⟫ : ℝ)
    rw [hxω, hfix]
    have h1 : (⟪ω, ω⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hωn]; norm_num
    rw [h1]; exact hb_mem.2.le
  · have hxnp : x ≠ -ω := by
      intro heq
      rw [heq, inner_neg_left] at hxm
      have h1 : (⟪ω, ω⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hωn]; norm_num
      rw [h1] at hxm
      linarith [hm_gt]
    have hratemono : min m₀ (⟪ω, z₀⟫ : ℝ) ≤ min (⟪x, z₀⟫ : ℝ) (⟪ω, z₀⟫ : ℝ) :=
      min_le_min hxm₀ le_rfl
    have hqpos : 0 ≤ max 1 q := le_trans zero_le_one (le_max_left _ _)
    have hrate2 : 2 * (max 1 q * (min m₀ (⟪ω, z₀⟫ : ℝ) - cosR₀)) * T
        ≤ 2 * (max 1 q * (min (⟪x, z₀⟫ : ℝ) (⟪ω, z₀⟫ : ℝ) - cosR₀)) * T := by
      nlinarith [mul_le_mul_of_nonneg_left hratemono hqpos, hT.le]
    apply scaledGatedBlock_z0_reach (lt_of_lt_of_le one_pos (le_max_left 1 q)) hz₀n hωn
      hcosR₀_nonneg hT.le hxs hxω hxnp (by linarith [hxm₀, hm₀cap]) hωcap hb_mem
    have hqmul : q * (2 * (min m₀ (⟪ω, z₀⟫ : ℝ) - cosR₀) * T) = logOdds b - logOdds m := by
      rw [hq, div_mul_cancel₀]
      exact hden.ne'
    have hqle : q ≤ max 1 q := le_max_right _ _
    have hstep1 : logOdds b - logOdds m ≤ 2 * (max 1 q * (min m₀ (⟪ω, z₀⟫ : ℝ) - cosR₀)) * T := by
      calc logOdds b - logOdds m = q * (2 * (min m₀ (⟪ω, z₀⟫ : ℝ) - cosR₀) * T) := hqmul.symm
        _ ≤ max 1 q * (2 * (min m₀ (⟪ω, z₀⟫ : ℝ) - cosR₀) * T) :=
            mul_le_mul_of_nonneg_right hqle hden.le
        _ = 2 * (max 1 q * (min m₀ (⟪ω, z₀⟫ : ℝ) - cosR₀)) * T := by ring
    have hmono : logOdds m ≤ logOdds (⟪x, ω⟫ : ℝ) :=
      logOdds_le_logOdds ⟨hm_gt, hm_lt_one⟩ (inner_mem_Ioo_of_ne hxs hωs hxω hxnp) hxm
    linarith [hstep1, hrate2, hmono]

/-- **Two-cap retention, localized (union-form step 1 of `lemma_B_1`/`lemma_B_2`).** Faithful to
the paper's own Lemma B.2 construction (gate centered at `ℬ₀`'s own center `z₀`, not at the overlap
point `ω`): a single gated block funnels a `(1-ε)`-fraction of `ℬ₀`'s mass into `ℬ₀ ∩ ℬ₁`, *and*
fixes every on-sphere point outside `ℬ₀` pointwise. This last conjunct is exactly the piece
`gated_twoCap_retention` cannot state (its gate, centered at `ω`, only fixes points outside a cap
centered at `ω`, not outside `ℬ₀`) -- it is what the union-tracking induction for `lemma_B_1` needs
to know that earlier, already-placed pieces of the union are left untouched by each subsequent
step. -/
theorem gated_twoCap_retention_localized (μ : Measure (Eucl d)) [IsProbabilityMeasure μ]
    (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (z₀ z₁ : Eucl d) (hz₀ : z₀ ∈ sphere d) (hz₁ : z₁ ∈ sphere d) (R₀ R₁ : ℝ)
    (hR₀ : R₀ ∈ Set.Ioo 0 (Real.pi / 2)) (hR₁ : R₁ ∈ Set.Ioo 0 (Real.pi / 2))
    (hcap : (geodesicBall z₀ R₀ ∩ geodesicBall z₁ R₁).Nonempty) :
    ∃ θ : Params d, switches θ ≤ 1 ∧
      (1 - ENNReal.ofReal ε) * μ (geodesicBall z₀ R₀) ≤
        (Axioms.measureFlow θ T μ) (geodesicBall z₀ R₀ ∩ geodesicBall z₁ R₁) ∧
      ∀ x, x ∈ sphere d → x ∉ geodesicBall z₀ R₀ → flowMap θ T x = x := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  obtain ⟨ω, hω₀, hω₁⟩ := hcap
  have hωs : ω ∈ sphere d := hω₀.1
  have hωn : ‖ω‖ = 1 := norm_eq_one_of_mem_sphere hωs
  have hz₀n : ‖z₀‖ = 1 := norm_eq_one_of_mem_sphere hz₀
  set a₀ := geodesicDist z₀ ω with ha₀_def
  set a₁ := geodesicDist z₁ ω with ha₁_def
  have ha₀R : a₀ < R₀ := hω₀.2
  have ha₁R : a₁ < R₁ := hω₁.2
  have ha₀0 : 0 ≤ a₀ := (geodesicDist_mem_Icc z₀ ω).1
  have ha₁0 : 0 ≤ a₁ := (geodesicDist_mem_Icc z₁ ω).1
  set r := min (R₀ - a₀) (R₁ - a₁) / 2 with hr_def
  have hr_pos : 0 < r := by
    have h0 : 0 < R₀ - a₀ := sub_pos.mpr ha₀R
    have h1 : 0 < R₁ - a₁ := sub_pos.mpr ha₁R
    have : 0 < min (R₀ - a₀) (R₁ - a₁) := lt_min h0 h1
    positivity
  have hr_lt_pi : r < Real.pi := by
    have h0 : min (R₀ - a₀) (R₁ - a₁) ≤ R₀ - a₀ := min_le_left _ _
    have : r ≤ (R₀ - a₀) / 2 := by rw [hr_def]; linarith
    have hR₀π : R₀ < Real.pi / 2 := hR₀.2
    linarith
  have htarget : ∀ y, y ∈ sphere d → Real.cos r ≤ (⟪y, ω⟫ : ℝ) →
      y ∈ geodesicBall z₀ R₀ ∩ geodesicBall z₁ R₁ := by
    intro y hy hyr
    have hdy : geodesicDist ω y ≤ r := by
      refine geodesicDist_le_of_cos_le_inner hr_pos.le ?_
      rwa [real_inner_comm]
    have hrlt₀ : r < R₀ - a₀ := by
      have := min_le_left (R₀ - a₀) (R₁ - a₁)
      have h0 : 0 < min (R₀ - a₀) (R₁ - a₁) := lt_min (sub_pos.mpr ha₀R) (sub_pos.mpr ha₁R)
      rw [hr_def]; linarith
    have hrlt₁ : r < R₁ - a₁ := by
      have := min_le_right (R₀ - a₀) (R₁ - a₁)
      have h0 : 0 < min (R₀ - a₀) (R₁ - a₁) := lt_min (sub_pos.mpr ha₀R) (sub_pos.mpr ha₁R)
      rw [hr_def]; linarith
    refine ⟨⟨hy, ?_⟩, ⟨hy, ?_⟩⟩
    · calc geodesicDist z₀ y ≤ geodesicDist z₀ ω + geodesicDist ω y :=
            geodesicDist_triangle hz₀ hωs hy
        _ ≤ a₀ + r := add_le_add le_rfl hdy
        _ < R₀ := by linarith
    · calc geodesicDist z₁ y ≤ geodesicDist z₁ ω + geodesicDist ω y :=
            geodesicDist_triangle hz₁ hωs hy
        _ ≤ a₁ + r := add_le_add le_rfl hdy
        _ < R₁ := by linarith
  have hfcont : Continuous fun x : Eucl d => geodesicDist z₀ x := continuous_geodesicDist z₀
  have hopen : MeasurableSet {x : Eucl d | geodesicDist z₀ x < R₀} :=
    (isOpen_lt hfcont continuous_const).measurableSet
  have hfin : (μ.restrict (sphere d)) {x | geodesicDist z₀ x < R₀} ≠ ⊤ :=
    measure_ne_top _ _
  obtain ⟨r_sub, hr_sub_lt, hmass⟩ :=
    exists_closed_sublevel_mass_ge (μ := μ.restrict (sphere d)) hfcont hfin hε
  have hB₀eq : (μ.restrict (sphere d)) {x | geodesicDist z₀ x < R₀}
      = μ (geodesicBall z₀ R₀) := by
    rw [Measure.restrict_apply hopen]
    congr 1
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, geodesicBall]
    tauto
  have hSeq : (μ.restrict (sphere d)) {x | geodesicDist z₀ x ≤ r_sub}
      = μ {x | x ∈ sphere d ∧ geodesicDist z₀ x ≤ r_sub} := by
    rw [Measure.restrict_apply (measurableSet_le hfcont.measurable measurable_const)]
    congr 1
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    tauto
  set ρ := max r_sub 0 with hρ_def
  have hρR : ρ < R₀ := max_lt hr_sub_lt hR₀.1
  have hρnn : 0 ≤ ρ := le_max_right _ _
  set D := a₀ + ρ with hD_def
  have hD_lt : D < Real.pi := by
    have hR₀π : R₀ < Real.pi / 2 := hR₀.2
    have : D < R₀ + R₀ := by
      have := ha₀R; rw [hD_def]; linarith
    linarith
  set D' := max D (r / 2) with hD'_def
  have hD'_pos : 0 < D' := lt_of_lt_of_le (half_pos hr_pos) (le_max_right _ _)
  have hD'_lt : D' < Real.pi := by
    refine max_lt hD_lt ?_
    linarith
  set m := Real.cos D' with hm_def
  have hm_lt_one : m < 1 := by
    have := Real.strictAntiOn_cos (Set.left_mem_Icc.mpr hπ.le)
      ⟨hD'_pos.le, hD'_lt.le⟩ hD'_pos
    simpa [hm_def] using this
  have hm_gt : (-1 : ℝ) < m := by
    have := Real.strictAntiOn_cos ⟨hD'_pos.le, hD'_lt.le⟩
      (Set.right_mem_Icc.mpr hπ.le) hD'_lt
    simpa [hm_def] using this
  have hsub_source_ω : {x | x ∈ sphere d ∧ geodesicDist z₀ x ≤ r_sub}
      ⊆ {x | x ∈ sphere d ∧ m ≤ (⟪x, ω⟫ : ℝ)} := by
    rintro x ⟨hxs, hxd⟩
    refine ⟨hxs, ?_⟩
    have hdx : geodesicDist ω x ≤ D' := by
      calc geodesicDist ω x ≤ geodesicDist ω z₀ + geodesicDist z₀ x :=
            geodesicDist_triangle hωs hz₀ hxs
        _ = a₀ + geodesicDist z₀ x := by rw [geodesicDist_comm ω z₀]
        _ ≤ a₀ + ρ := add_le_add le_rfl (hxd.trans (le_max_left _ _))
        _ ≤ D' := le_max_left _ _
    have hcos := cos_le_inner_of_geodesicDist_le hωs hxs hD'_lt.le hdx
    rw [real_inner_comm] at hcos
    exact hcos
  set m₀ := Real.cos ρ with hm₀_def
  have hsub_source_z₀ : {x | x ∈ sphere d ∧ geodesicDist z₀ x ≤ r_sub}
      ⊆ {x | x ∈ sphere d ∧ m₀ ≤ (⟪x, z₀⟫ : ℝ)} := by
    rintro x ⟨hxs, hxd⟩
    refine ⟨hxs, ?_⟩
    have hxdρ : geodesicDist z₀ x ≤ ρ := hxd.trans (hρ_def ▸ le_max_left _ _)
    have hρpi : ρ ≤ Real.pi := by linarith [hR₀.2]
    have hle : Real.cos ρ ≤ (⟪z₀, x⟫ : ℝ) := cos_le_inner_of_geodesicDist_le hz₀ hxs hρpi hxdρ
    rw [real_inner_comm] at hle
    exact hle
  set cosR₀ := Real.cos R₀ with hcosR₀_def
  have hR₀pi : R₀ ≤ Real.pi := by linarith [hR₀.2]
  have hρpi : ρ ≤ Real.pi := by linarith [hR₀.2]
  have hcosR₀_nonneg : 0 ≤ cosR₀ := by
    rw [hcosR₀_def]
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [hR₀.1], by linarith [hR₀.2]⟩
  have hm₀cap : cosR₀ < m₀ := by
    have hlt : Real.cos R₀ < Real.cos ρ :=
      Real.strictAntiOn_cos ⟨hρnn, hρpi⟩ ⟨hρnn.trans hρR.le, hR₀pi⟩ hρR
    rw [hcosR₀_def, hm₀_def]; linarith
  have hωcap : cosR₀ < (⟪ω, z₀⟫ : ℝ) := by
    have hle : Real.cos a₀ ≤ (⟪z₀, ω⟫ : ℝ) :=
      cos_le_inner_of_geodesicDist_le hz₀ hωs (ha₀R.le.trans hR₀pi) le_rfl
    rw [real_inner_comm] at hle
    have hlt : Real.cos R₀ < Real.cos a₀ :=
      Real.strictAntiOn_cos ⟨ha₀0, ha₀R.le.trans hR₀pi⟩ ⟨ha₀0.trans ha₀R.le, hR₀pi⟩ ha₀R
    rw [hcosR₀_def]; linarith
  set b := Real.cos r with hb_def
  have hb_mem : b ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · have := Real.strictAntiOn_cos ⟨hr_pos.le, hr_lt_pi.le⟩
        (Set.right_mem_Icc.mpr hπ.le) hr_lt_pi
      simpa [hb_def] using this
    · have := Real.strictAntiOn_cos (Set.left_mem_Icc.mpr hπ.le)
        ⟨hr_pos.le, hr_lt_pi.le⟩ hr_pos
      simpa [hb_def] using this
  obtain ⟨A, hA, hmaps⟩ := exists_scaledGatedBlock_z0_mapsTo_cap hz₀n hωn hT hcosR₀_nonneg
    hm₀cap hωcap hm_gt hm_lt_one hb_mem hωs
  set B := scaledGatedBlock hA.le hz₀n hωn (by linarith : (-1:ℝ) ≤ cosR₀) hT.le with hB_def
  refine ⟨[B], ?_, ?_, ?_⟩
  · show switches [B] ≤ 1
    simp [switches]
  · have hflow_eq : flowMap [B] T = B.blockFlow T := rfl
    have hmaps' : Set.MapsTo (flowMap [B] T)
        {x | x ∈ sphere d ∧ geodesicDist z₀ x ≤ r_sub}
        (geodesicBall z₀ R₀ ∩ geodesicBall z₁ R₁) := by
      intro x hx
      have hxω : x ∈ {x | x ∈ sphere d ∧ m ≤ (⟪x, ω⟫ : ℝ)} := hsub_source_ω hx
      have hxz₀ : x ∈ {x | x ∈ sphere d ∧ m₀ ≤ (⟪x, z₀⟫ : ℝ)} := hsub_source_z₀ hx
      have h1 : b ≤ (⟪B.blockFlow T x, ω⟫ : ℝ) := hmaps ⟨hx.1, hxω.2, hxz₀.2⟩
      have hsphere : B.blockFlow T x ∈ sphere d := B.blockFlow_mem_sphere hx.1 hT.le
      rw [hflow_eq]
      exact htarget _ hsphere h1
    have hmeasB : MeasurableSet (geodesicBall z₀ R₀ ∩ geodesicBall z₁ R₁) :=
      (measurableSet_geodesicBall _ _).inter (measurableSet_geodesicBall _ _)
    have hbridge := Axioms.le_measureFlow_of_mapsTo [B] hT.le μ hmeasB hmaps'
    calc (1 - ENNReal.ofReal ε) * μ (geodesicBall z₀ R₀)
        = (1 - ENNReal.ofReal ε)
            * (μ.restrict (sphere d)) {x | geodesicDist z₀ x < R₀} := by rw [hB₀eq]
      _ ≤ (μ.restrict (sphere d)) {x | geodesicDist z₀ x ≤ r_sub} := hmass
      _ = μ {x | x ∈ sphere d ∧ geodesicDist z₀ x ≤ r_sub} := hSeq
      _ ≤ (Axioms.measureFlow [B] T μ) (geodesicBall z₀ R₀ ∩ geodesicBall z₁ R₁) := hbridge
  · intro x hxs hxout
    have hflow_eq : flowMap [B] T = B.blockFlow T := rfl
    rw [hflow_eq]
    have hgd : R₀ ≤ geodesicDist z₀ x := by
      by_contra hlt
      push_neg at hlt
      exact hxout ⟨hxs, hlt⟩
    have hle : (⟪z₀, x⟫ : ℝ) ≤ cosR₀ := by
      rw [hcosR₀_def, ← cos_geodesicDist hz₀ hxs]
      exact Real.cos_le_cos_of_nonneg_of_le_pi hR₀.1.le (geodesicDist_mem_Icc z₀ x).2 hgd
    exact scaledGatedBlock_z0_fixed_of_le hA.le hz₀n hωn (by linarith : (-1:ℝ) ≤ cosR₀) hT.le hle T

end MeasureToMeasure.Leaves
