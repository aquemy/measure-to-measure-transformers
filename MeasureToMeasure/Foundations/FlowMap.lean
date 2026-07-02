import MeasureToMeasure.Foundations.SphereFlow
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall

/-!
# The mean-field flow map (M3): the per-block characteristic flow

The continuity equation (1.2)-(1.3) transports mass along the characteristics `ẋ = V(x)` of a
layer-normalized velocity field. This file builds the flow map `Φ_θ^t` that `Axioms/*` currently
axiomatize, discharging the M3 milestone at its faithful primitive point.

The key modeling choice is what a **block** is. Rather than fixing one algebraic velocity field, a
`Block` bundles the *well-posedness data* the flow actually needs: a **globally-Lipschitz** velocity
field that is **radially tangent** (`⟪x, V x⟫ = gate x · (‖x‖² − 1)`, so `V` is tangent on the unit
sphere and its flow preserves the sphere), plus a nonnegative **duration**. The paper's per-block
fields -- the ReLU-gated projected field `P_x^⊥((cos R − ⟪z,x⟫)_+ • ω)` (B.5) and the barycenter
field `P_x^⊥(⟪𝔼_μ[x],α⟫ • α)` (B.9) -- are *instances* of a `Block` (after a cutoff off the sphere
makes them globally Lipschitz; the quadratic projector is only locally Lipschitz). Isolating the
well-posedness this way is what lets the flow map, its Lipschitz/bijectivity/semigroup/parked laws,
and the schedule algebra all be *proved* from the autonomous-field lemmas in `SphereFlow.lean` plus
Mathlib's `IsPicardLindelof.of_time_independent`.
-/

namespace MeasureToMeasure

open scoped RealInnerProductSpace NNReal
open Set

variable {d : ℕ}

/-- A **well-posed velocity block** for the characteristic flow: a globally-Lipschitz, radially
tangent velocity field on `ℝ^d` together with a nonnegative time duration. Concrete (a `structure`,
not an axiom), so `Params := List (Block d)` makes the schedule algebra -- composition as
concatenation, identity as the empty list, reversal as `List.reverse` -- provable rather than
assumed. -/
structure Block (d : ℕ) where
  /-- the velocity field, taken already globally Lipschitz (e.g. the paper's field cut off away from
  the sphere, where the raw quadratic projector would only be locally Lipschitz). -/
  field : Eucl d → Eucl d
  /-- a global Lipschitz constant for `field`. -/
  lipConst : ℝ≥0
  /-- `field` is globally `lipConst`-Lipschitz -- the hypothesis Picard-Lindelöf needs. -/
  lipschitz : LipschitzWith lipConst field
  /-- a global bound on `field`. The paper's cutoff field is bounded; global boundedness is what makes
  Picard-Lindelöf existence hold on the *whole* interval `[0, dur]` (the ball radius can be taken
  `bound · dur` larger without the field's bound growing with it). -/
  bound : ℝ≥0
  /-- `field` is globally bounded by `bound`. -/
  field_le : ∀ x, ‖field x‖ ≤ bound
  /-- the radial **gate** `c(x)`: `⟪x, field x⟫ = c(x) · (‖x‖² − 1)`. On the sphere this is `0`, i.e.
  `field` is tangent; off the sphere `c` measures the radial drift the Grönwall argument controls. -/
  gate : Eucl d → ℝ
  /-- a uniform bound on twice the gate, feeding the Grönwall sphere-invariance estimate. -/
  gateBound : ℝ
  /-- the uniform gate bound holds everywhere. -/
  gate_le : ∀ x, |2 * gate x| ≤ gateBound
  /-- the radial-tangency identity that makes the flow preserve the sphere. -/
  radial : ∀ x, (⟪x, field x⟫ : ℝ) = gate x * (‖x‖ ^ 2 - 1)
  /-- the block's time duration. -/
  dur : ℝ
  /-- durations are nonnegative. -/
  dur_nonneg : 0 ≤ dur

/-- A **parameter schedule** is a finite list of blocks. Concatenation is composition of flows, the
empty list is the identity schedule, and the list length is the switch (depth) count. -/
abbrev Params (d : ℕ) : Type := List (Block d)

/-- The number of parameter switches of a schedule: its block count (Section 1.4.3 depth proxy). -/
def switches (θ : Params d) : ℕ := θ.length

/-!
## Per-block existence (Picard-Lindelöf)

The block's autonomous field is globally bounded and globally Lipschitz, so Picard-Lindelöf holds on
the *whole* symmetric interval `[-T, T]` around any point: taking the ball radius `bound·T + r`, the
global bound `‖field‖ ≤ bound` keeps the well-posedness constant from growing with the radius, so the
interval condition `L·T ≤ a - r` is met with equality. This is what sidesteps the missing global-
existence continuation -- boundedness on a fixed time interval is enough.
-/

/-- **Picard-Lindelöf for a block's field** on `[-T, T]` around `x₀`, for any radius `r`. Global
boundedness (`field_le`) and global Lipschitzness supply the three `of_time_independent` hypotheses;
the interval condition holds with equality by the choice `a = bound·T + r`. -/
theorem Block.isPicardLindelof (b : Block d) (x₀ : Eucl d) (T r : ℝ≥0) :
    IsPicardLindelof (fun _ => b.field)
      (⟨0, Set.mem_Icc.mpr ⟨neg_nonpos.mpr T.coe_nonneg, T.coe_nonneg⟩⟩ : Set.Icc (-(T : ℝ)) T)
      x₀ (b.bound * T + r) r b.bound b.lipConst := by
  apply IsPicardLindelof.of_time_independent
  · intro x _; exact b.field_le x
  · exact b.lipschitz.lipschitzOnWith
  · have hmax : max ((T : ℝ) - 0) (0 - -(T : ℝ)) = (T : ℝ) := by
      rw [sub_zero, zero_sub, neg_neg, max_self]
    rw [hmax]
    push_cast
    ring_nf
    rfl

/-- **Interval integral curve through `x₀`.** For any `T ≥ 0` there is a curve `α` with `α 0 = x₀`
that solves `ẋ = field x` on `[-T, T]`. The value at the block's duration is one point-flow step. -/
theorem Block.exists_integralCurveOn (b : Block d) (x₀ : Eucl d) (T : ℝ≥0) :
    ∃ α : ℝ → Eucl d, α 0 = x₀ ∧
      ∀ t ∈ Set.Icc (-(T : ℝ)) T, HasDerivWithinAt α (b.field (α t)) (Set.Icc (-(T : ℝ)) T) t := by
  have hx : x₀ ∈ Metric.closedBall x₀ ((0 : ℝ≥0) : ℝ) := by simp
  obtain ⟨α, hα0, hαderiv⟩ :=
    (b.isPicardLindelof x₀ T 0).exists_eq_forall_mem_Icc_hasDerivWithinAt hx
  exact ⟨α, hα0, hαderiv⟩

/-!
## The global point flow

The interval solutions are glued into a single global integral curve through each point. Two solutions
of the same autonomous globally-Lipschitz field that agree at one time agree on the whole open interval
(`ODE_solution_unique_of_mem_Ioo` with `s ≡ univ`), so the family of `[-n, n]` solutions is coherent;
choosing, for each `t`, a solution on an interval strictly containing `t` gives a total function that
is locally a genuine solution, hence an `IsIntegralCurve` on all of `ℝ`.
-/

/-- **Interval uniqueness for a block's field.** Two solutions of `ẋ = field x` on `Ioo a c` that agree
at a point of the interval agree throughout it. -/
theorem Block.integralCurve_eqOn (b : Block d) {α β : ℝ → Eucl d} {a c t₀ : ℝ}
    (hα : ∀ t ∈ Set.Ioo a c, HasDerivAt α (b.field (α t)) t)
    (hβ : ∀ t ∈ Set.Ioo a c, HasDerivAt β (b.field (β t)) t)
    (ht₀ : t₀ ∈ Set.Ioo a c) (h0 : α t₀ = β t₀) :
    Set.EqOn α β (Set.Ioo a c) :=
  ODE_solution_unique_of_mem_Ioo (v := fun _ => b.field) (s := fun _ => Set.univ)
    (K := b.lipConst) (fun _ _ => b.lipschitz.lipschitzOnWith) ht₀
    (fun t ht => ⟨hα t ht, Set.mem_univ _⟩) (fun t ht => ⟨hβ t ht, Set.mem_univ _⟩) h0

/-- **Global integral curve through `x`.** Gluing the interval solutions gives a curve `Φ` with
`Φ 0 = x` solving `ẋ = field x` for all time -- the point flow of a block. -/
theorem Block.exists_globalIntegralCurve (b : Block d) (x : Eucl d) :
    ∃ Φ : ℝ → Eucl d, Φ 0 = x ∧ IsIntegralCurve Φ (fun _ => b.field) := by
  classical
  -- interval solutions through `x` on the open interval `(-n, n)`, as genuine `HasDerivAt`
  have hex : ∀ n : ℕ, ∃ α : ℝ → Eucl d, α 0 = x ∧
      ∀ t ∈ Set.Ioo (-(n : ℝ)) n, HasDerivAt α (b.field (α t)) t := by
    intro n
    obtain ⟨α, h0, hd⟩ := b.exists_integralCurveOn x (n : ℝ≥0)
    refine ⟨α, h0, fun t ht => ?_⟩
    have hcoe : ((n : ℝ≥0) : ℝ) = (n : ℝ) := by push_cast; ring
    have hmem : t ∈ Set.Icc (-((n : ℝ≥0) : ℝ)) ((n : ℝ≥0) : ℝ) := by
      rw [hcoe]; exact Set.Ioo_subset_Icc_self ht
    have hnhds : Set.Icc (-((n : ℝ≥0) : ℝ)) ((n : ℝ≥0) : ℝ) ∈ nhds t := by
      rw [hcoe]; exact Icc_mem_nhds ht.1 ht.2
    exact (hd t hmem).hasDerivAt hnhds
  choose α hα0 hαd using hex
  -- coherence: for `m ≤ n`, the two solutions agree on `(-m, m)`
  have hcoh : ∀ m n : ℕ, m ≤ n → ∀ t ∈ Set.Ioo (-(m : ℝ)) m, α m t = α n t := by
    intro m n hmn t ht
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hmpos : (0 : ℝ) < (m : ℝ) := by linarith [ht.1, ht.2]
    have hsub : Set.Ioo (-(m : ℝ)) m ⊆ Set.Ioo (-(n : ℝ)) n :=
      Set.Ioo_subset_Ioo (by linarith) hmn'
    exact b.integralCurve_eqOn (fun s hs => hαd m s hs) (fun s hs => hαd n s (hsub hs))
      (Set.mem_Ioo.mpr ⟨by linarith, hmpos⟩) (by rw [hα0 m, hα0 n]) ht
  -- the total curve: at `t`, use the solution on `(-N t, N t)` with `N t := ⌈|t|⌉₊ + 1 > |t|`
  set N : ℝ → ℕ := fun t => ⌈|t|⌉₊ + 1 with hN
  have hNgt : ∀ t : ℝ, |t| < (N t : ℝ) := by
    intro t
    have h1 : |t| ≤ (⌈|t|⌉₊ : ℝ) := Nat.le_ceil _
    have hcast : (N t : ℝ) = (⌈|t|⌉₊ : ℝ) + 1 := by simp only [hN]; push_cast; ring
    rw [hcast]; linarith
  have htmem : ∀ t : ℝ, t ∈ Set.Ioo (-(N t : ℝ)) (N t : ℝ) :=
    fun t => Set.mem_Ioo.mpr (abs_lt.mp (hNgt t))
  refine ⟨fun t => α (N t) t, hα0 (N 0), ?_⟩
  rw [isIntegralCurve_iff_isIntegralCurveAt]
  intro t
  -- on the open interval `(-(N t), N t)` the total curve agrees with `α (N t)`, by coherence
  have hUnhds : Set.Ioo (-(N t : ℝ)) (N t) ∈ nhds t := (isOpen_Ioo).mem_nhds (htmem t)
  have hagree : Set.EqOn (fun u => α (N u) u) (α (N t)) (Set.Ioo (-(N t : ℝ)) (N t)) := by
    intro s hs
    rcases le_total (N s) (N t) with h | h
    · exact hcoh (N s) (N t) h s (htmem s)
    · exact (hcoh (N t) (N s) h s hs).symm
  refine IsIntegralCurveOn.isIntegralCurveAt (fun s hs => ?_) hUnhds
  have hd : HasDerivAt (α (N t)) (b.field (α (N t) s)) s := hαd (N t) s hs
  have hee : (fun u => α (N u) u) =ᶠ[nhds s] (α (N t)) :=
    Filter.eventuallyEq_of_mem ((isOpen_Ioo).mem_nhds hs) hagree
  have key : HasDerivAt (fun u => α (N u) u) (b.field (α (N t) s)) s := hd.congr_of_eventuallyEq hee
  have hfe : b.field (α (N t) s) = b.field ((fun u => α (N u) u) s) := by rw [hagree hs]
  rw [hfe] at key
  exact key.hasDerivWithinAt

/-!
## The point flow map of a block

`blockFlow b t x` is the value at time `t` of the (unique) integral curve through `x`. From the
autonomous-field algebra of `SphereFlow.lean` it is the identity at `t = 0`, a one-parameter group
(`blockFlow t ∘ blockFlow s = blockFlow (s+t)`), injective at every time, and preserves the sphere.
-/

/-- The global integral curve through `x` (choice of `exists_globalIntegralCurve`). -/
noncomputable def Block.blockCurve (b : Block d) (x : Eucl d) : ℝ → Eucl d :=
  (b.exists_globalIntegralCurve x).choose

theorem Block.blockCurve_zero (b : Block d) (x : Eucl d) : b.blockCurve x 0 = x :=
  (b.exists_globalIntegralCurve x).choose_spec.1

theorem Block.blockCurve_isIntegralCurve (b : Block d) (x : Eucl d) :
    IsIntegralCurve (b.blockCurve x) (fun _ => b.field) :=
  (b.exists_globalIntegralCurve x).choose_spec.2

/-- The **point flow** of a block: `blockFlow b t x` transports `x` along the field for time `t`. -/
noncomputable def Block.blockFlow (b : Block d) (t : ℝ) (x : Eucl d) : Eucl d := b.blockCurve x t

@[simp] theorem Block.blockFlow_zero (b : Block d) (x : Eucl d) : b.blockFlow 0 x = x :=
  b.blockCurve_zero x

theorem Block.blockFlow_zero_eq_id (b : Block d) : b.blockFlow 0 = id := by
  funext x; exact b.blockFlow_zero x

/-- **Semigroup law.** Flowing for `s` and then for `t` equals flowing for `s + t`. -/
theorem Block.blockFlow_add (b : Block d) (s t : ℝ) (x : Eucl d) :
    b.blockFlow t (b.blockFlow s x) = b.blockFlow (s + t) x := by
  have h := integralCurve_semigroup b.lipschitz (b.blockCurve_isIntegralCurve x)
    (b.blockCurve_isIntegralCurve (b.blockCurve x s)) s (b.blockCurve_zero _)
  simpa only [Block.blockFlow] using h t

/-- **Injectivity** of the time-`t` point flow: two curves agreeing at time `t` agree at time `0`. -/
theorem Block.blockFlow_injective (b : Block d) (t : ℝ) : Function.Injective (b.blockFlow t) := by
  intro x y hxy
  have hx : IsIntegralCurve (fun s => b.blockCurve x (t + s)) (fun _ => b.field) :=
    integralCurve_comp_add (b.blockCurve_isIntegralCurve x) t
  have hy : IsIntegralCurve (fun s => b.blockCurve y (t + s)) (fun _ => b.field) :=
    integralCurve_comp_add (b.blockCurve_isIntegralCurve y) t
  have h0 : (fun s => b.blockCurve x (t + s)) 0 = (fun s => b.blockCurve y (t + s)) 0 := by
    simp only [add_zero]; exact hxy
  have heq := integralCurve_unique b.lipschitz hx hy h0
  have := congrFun heq (-t)
  simpa only [add_neg_cancel, b.blockCurve_zero] using this

/-- **Sphere invariance.** If `x` is on the unit sphere, so is `blockFlow b t x` for all `t ≥ 0`
(the radial-tangency identity plus the uniform gate bound feed the Grönwall argument). -/
theorem Block.blockFlow_mem_sphere (b : Block d) {x : Eucl d} (hx : x ∈ sphere d) {t : ℝ}
    (ht : 0 ≤ t) : b.blockFlow t x ∈ sphere d := by
  have hnorm := norm_sq_eq_one_of_radial_tangent
    (x := b.blockCurve x) (v := fun s => b.field (b.blockCurve x s))
    (c := fun s => b.gate (b.blockCurve x s)) (K := b.gateBound) (T := t)
    (fun s _ => b.blockCurve_isIntegralCurve x s)
    (fun s _ => b.radial (b.blockCurve x s))
    (fun s _ => b.gate_le (b.blockCurve x s))
    (by rw [b.blockCurve_zero x]; exact norm_eq_one_of_mem_sphere hx)
  have hb : ‖b.blockCurve x t‖ = 1 := hnorm t ⟨ht, le_refl t⟩
  simpa only [sphere, Metric.mem_sphere, dist_eq_norm, sub_zero, Block.blockFlow] using hb

/-- **Bijectivity** of the time-`t` point flow, with inverse the time-`(-t)` flow. -/
theorem Block.blockFlow_bijective (b : Block d) (t : ℝ) : Function.Bijective (b.blockFlow t) :=
  ⟨b.blockFlow_injective t,
    fun y => ⟨b.blockFlow (-t) y, by rw [b.blockFlow_add]; simp⟩⟩

/-- The time-`(-t)` flow is a left inverse of the time-`t` flow: `Φ^{-t} ∘ Φ^t = id`. -/
theorem Block.blockFlow_neg_comp (b : Block d) (t : ℝ) (x : Eucl d) :
    b.blockFlow (-t) (b.blockFlow t x) = x := by rw [b.blockFlow_add]; simp

/-- **Grönwall dependence on the initial value.** For `t ≥ 0` the point flow spreads distances by at
most `e^{K t}`: `dist (Φ^t x) (Φ^t y) ≤ dist x y · e^{K t}`. -/
theorem Block.blockFlow_dist_le (b : Block d) {t : ℝ} (ht : 0 ≤ t) (x y : Eucl d) :
    dist (b.blockFlow t x) (b.blockFlow t y) ≤ dist x y * Real.exp (b.lipConst * t) := by
  have h := integralCurve_dist_le b.lipschitz (b.blockCurve_isIntegralCurve x)
    (b.blockCurve_isIntegralCurve y) ht
  simpa only [b.blockCurve_zero, Block.blockFlow] using h

/-- The point flow is Lipschitz (hence continuous and measurable) in the initial value, for `t ≥ 0`. -/
theorem Block.lipschitzWith_blockFlow (b : Block d) {t : ℝ} (ht : 0 ≤ t) :
    LipschitzWith (Real.exp (b.lipConst * t)).toNNReal (b.blockFlow t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.coe_toNNReal _ (Real.exp_nonneg _), mul_comm]
  exact b.blockFlow_dist_le ht x y

theorem Block.continuous_blockFlow (b : Block d) {t : ℝ} (ht : 0 ≤ t) :
    Continuous (b.blockFlow t) := (b.lipschitzWith_blockFlow ht).continuous

theorem Block.measurable_blockFlow (b : Block d) {t : ℝ} (ht : 0 ≤ t) :
    Measurable (b.blockFlow t) := (b.continuous_blockFlow ht).measurable

end MeasureToMeasure
