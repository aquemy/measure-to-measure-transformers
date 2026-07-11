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

end MeasureToMeasure.Leaves
