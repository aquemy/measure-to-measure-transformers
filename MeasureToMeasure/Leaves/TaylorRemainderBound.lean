import MeasureToMeasure.Foundations.AttnStepExistence
import MeasureToMeasure.Leaves.BarycenterBoundaryGap
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A uniform `O(τ²)` Taylor remainder for the barycenter-alignment phase (Lemma 3.4 Part 2 leaf 2)

The paper's Appendix B.3 (p.36) Phase 1 construction for `lemma_3_4_part2` runs the SAME
constant-in-time self-attention block (`V = I_d`, `B = W = U = b = 0`, i.e. the field reduces to
`x ↦ P_x^⊥(E_μ[x])`, the tangential projection of the barycenter) independently on `μ` and `ν`, and
compares two trajectories from a shared point via a small-`τ` Taylor/Duhamel expansion. This leaf
builds that expansion as a genuine, UNIFORM (not just pointwise-in-`x`) `O(τ²)` remainder bound:

`‖Φ(τ,x) - x - τ • P_x^⊥(E_{μ0}[x])‖ ≤ 3τ²` for every `x` on the sphere, `τ ∈ [0,T]`.

The route ("Route 1′"): the Fundamental Theorem of Calculus gives
`Φ(τ,x) - x = ∫₀^τ field(μ0.map(Φ s), Φ s x) ds`; subtracting the constant `τ • field(μ0, x)` and
bounding the integrand's deviation via the projector's nonexpansiveness in its vector argument
(`norm_tangentialProjector_le`, giving the barycenter-drift term `≤ s`) and the projector's
base-point Lipschitz modulus (`norm_tangentialProjector_sub_point_le`, giving the trajectory-drift
term `≤ 2s`) yields an `O(s)` bound on the integrand UNIFORMLY over `x ∈ supp μ0` (in fact over all
of the sphere), hence `O(τ²)` after integrating over `[0,τ]`. This sidesteps the paper's construction
of a specific extremal boundary point via new geodesic-hull machinery: any point can serve, with the
uniform bound converting `[[leaf-1]]`'s strict inequality gap into an `O(τ)`-margin advantage that
survives the `O(τ²)` remainder for small enough `τ`.

M3b/mid-level staging: consumed when `lemma_3_4_part2` is discharged; see `Statements/MidLevel.lean`.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Set
open scoped RealInnerProductSpace NNReal Classical
open MeasureToMeasure.Foundations

variable {d : ℕ}

/-- The `AttnParams` instance for the paper's Phase 1 barycenter-alignment block: `V = I_d`,
`B = W = U = b = 0`, running for duration `T`. -/
noncomputable def pAlign (T : ℝ) (hT : 0 ≤ T) : AttnParams d where
  V := ContinuousLinearMap.id ℝ (Eucl d)
  B := 0
  W := 0
  U := 0
  b := 0
  duration := T
  duration_nonneg := hT

@[simp] theorem pAlign_duration (T : ℝ) (hT : 0 ≤ T) : (pAlign (d := d) T hT).duration = T := rfl

/-- With `B = 0`, `attnAvg` collapses to the plain barycenter (`attnAvg_zero_left`), and with
`V = I_d`, `W = 0` the field reduces to the tangential projection of the barycenter. -/
theorem pAlign_field (T : ℝ) (hT : 0 ≤ T) (ν : Measure (Eucl d)) [IsProbabilityMeasure ν]
    (x : Eucl d) :
    (pAlign (d := d) T hT).field ν x = tangentialProjector x (barycenter ν) := by
  unfold AttnParams.field pAlign
  simp only [ContinuousLinearMap.id_apply, zero_apply, reluVec]
  rw [attnAvg_zero_left]
  simp [barycenter]

theorem tangentialProjector_sub_right (x v w : Eucl d) :
    tangentialProjector x v - tangentialProjector x w = tangentialProjector x (v - w) := by
  simp only [tangentialProjector_apply, inner_sub_right, sub_smul]
  abel

theorem norm_pAlign_field_le (T : ℝ) (hT : 0 ≤ T) (ν : Measure (Eucl d)) [IsProbabilityMeasure ν]
    (hνs : ν (sphere d)ᶜ = 0) (hνint : Integrable (fun x : Eucl d => x) ν)
    {x : Eucl d} (hx : x ∈ sphere d) :
    ‖(pAlign (d := d) T hT).field ν x‖ ≤ 1 := by
  rw [pAlign_field]
  calc ‖tangentialProjector x (barycenter ν)‖ ≤ ‖barycenter ν‖ := norm_tangentialProjector_le hx _
    _ ≤ 1 := norm_barycenter_le_one hνs hνint

/-- The pushforward under a `pAlign`-flow of a sphere-supported probability measure is again a
sphere-supported probability measure (`sphere_bijOn` + `measurable`, both from `IsMeanFieldFlow`). -/
theorem pAlign_map_probSphere (T : ℝ) (hT : 0 ≤ T) (μ0 : Measure (Eucl d)) [IsProbabilityMeasure μ0]
    (hs : μ0 (sphere d)ᶜ = 0)
    (Φ : ℝ → Eucl d → Eucl d) (hΦ : IsMeanFieldFlow (pAlign T hT) μ0 Φ)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    IsProbabilityMeasure (μ0.map (Φ t)) ∧ (μ0.map (Φ t)) (sphere d)ᶜ = 0 := by
  have ht' : t ∈ Set.Icc (0:ℝ) (pAlign (d := d) T hT).duration := by simpa using ht
  have hmeas : Measurable (Φ t) := hΦ.measurable t ht'
  refine ⟨Measure.isProbabilityMeasure_map hmeas.aemeasurable, ?_⟩
  have hMS : MeasurableSet (sphere d)ᶜ := (Metric.isClosed_sphere.measurableSet).compl
  rw [Measure.map_apply hmeas hMS]
  apply measure_mono_null _ hs
  intro y hy hymem
  exact hy ((hΦ.sphere_bijOn t ht').mapsTo hymem)

/-- The field-along-trajectory function `s ↦ field(μ0.map(Φ s), Φ s x)` is interval-integrable on
`[0,τ]`: continuity of `s ↦ Φ s x` comes from `HasDerivAt` (`hΦ.deriv`) everywhere on `[0,T]`;
continuity of `s ↦ barycenter(μ0.map(Φ s))` comes from dominated convergence
(`continuousOn_of_dominated`, dominating by the sphere norm bound `1`); jointly this gives continuity
of the field itself (`tangentialProjector` is jointly continuous), hence `AEStronglyMeasurable`, and
boundedness by `1` (`norm_pAlign_field_le`) gives integrability. -/
theorem intervalIntegrable_pAlign_field_traj (T : ℝ) (hT : 0 ≤ T) (μ0 : Measure (Eucl d))
    [IsProbabilityMeasure μ0] (hs : μ0 (sphere d)ᶜ = 0)
    (Φ : ℝ → Eucl d → Eucl d) (hΦ : IsMeanFieldFlow (pAlign T hT) μ0 Φ)
    (x : Eucl d) (hx : x ∈ sphere d) {τ : ℝ} (hτ : τ ∈ Set.Icc (0:ℝ) T) :
    IntervalIntegrable (fun s => (pAlign T hT).field (μ0.map (Φ s)) (Φ s x)) volume 0 τ := by
  have hτpos : 0 ≤ τ := hτ.1
  have hcont_traj : ∀ y ∈ sphere d, ContinuousOn (fun s => Φ s y) (Set.uIcc (0:ℝ) τ) := by
    intro y hy s hs'
    have hsT : s ∈ Set.Icc (0:ℝ) T := by
      rw [Set.uIcc_of_le hτpos] at hs'
      exact ⟨hs'.1, le_trans hs'.2 hτ.2⟩
    exact (hΦ.deriv y hy s (by simpa using hsT)).continuousAt.continuousWithinAt
  have hmaps : ∀ s ∈ Set.Icc (0:ℝ) T, ∀ᵐ y ∂μ0, Φ s y ∈ sphere d := by
    intro s hsT
    filter_upwards [hs] with y hy
    exact (hΦ.sphere_bijOn s hsT).mapsTo hy
  have hcont_bary : ContinuousOn (fun s => barycenter (μ0.map (Φ s))) (Set.uIcc (0:ℝ) τ) := by
    have heq : ∀ s ∈ Set.uIcc (0:ℝ) τ, barycenter (μ0.map (Φ s)) = ∫ y, Φ s y ∂μ0 := by
      intro s hs'
      have hsT : s ∈ Set.Icc (0:ℝ) T := by
        rw [Set.uIcc_of_le hτpos] at hs'
        exact ⟨hs'.1, le_trans hs'.2 hτ.2⟩
      have hmeas : Measurable (Φ s) := hΦ.measurable s (by simpa using hsT)
      show ∫ y, y ∂(μ0.map (Φ s)) = ∫ y, Φ s y ∂μ0
      exact integral_map hmeas.aemeasurable aestronglyMeasurable_id
    apply ContinuousOn.congr _ heq
    apply MeasureTheory.continuousOn_of_dominated (bound := fun _ => (1 : ℝ))
    · intro s hs'
      have hsT : s ∈ Set.Icc (0:ℝ) T := by
        rw [Set.uIcc_of_le hτpos] at hs'
        exact ⟨hs'.1, le_trans hs'.2 hτ.2⟩
      exact (hΦ.measurable s (by simpa using hsT)).aestronglyMeasurable
    · intro s hs'
      have hsT : s ∈ Set.Icc (0:ℝ) T := by
        rw [Set.uIcc_of_le hτpos] at hs'
        exact ⟨hs'.1, le_trans hs'.2 hτ.2⟩
      filter_upwards [hmaps s hsT] with y hy
      simp only [sphere, Metric.mem_sphere, dist_zero_right] at hy
      simp [hy]
    · exact integrable_const 1
    · filter_upwards [hs] with y hy
      exact hcont_traj y hy
  have hcont_field : ContinuousOn
      (fun s => (pAlign T hT).field (μ0.map (Φ s)) (Φ s x)) (Set.uIcc (0:ℝ) τ) := by
    have heqf : ∀ s ∈ Set.uIcc (0:ℝ) τ, (pAlign T hT).field (μ0.map (Φ s)) (Φ s x)
        = tangentialProjector (Φ s x) (barycenter (μ0.map (Φ s))) := by
      intro s hs'
      have hsT : s ∈ Set.Icc (0:ℝ) T := by
        rw [Set.uIcc_of_le hτpos] at hs'
        exact ⟨hs'.1, le_trans hs'.2 hτ.2⟩
      haveI : IsProbabilityMeasure (μ0.map (Φ s)) := (pAlign_map_probSphere T hT μ0 hs Φ hΦ hsT).1
      exact pAlign_field T hT _ _
    apply ContinuousOn.congr _ heqf
    have hcp : Continuous (fun p : Eucl d × Eucl d => tangentialProjector p.1 p.2) := by
      unfold tangentialProjector InnerProductGeometry.tangentialProjector
      fun_prop
    exact hcp.comp_continuousOn ((hcont_traj x hx).prodMk hcont_bary)
  apply IntervalIntegrable.mono_fun' (g := fun _ => (1:ℝ))
  · exact intervalIntegrable_const
  · exact (hcont_field.mono Set.uIoc_subset_uIcc).aestronglyMeasurable (μ := volume)
      measurableSet_uIoc
  · apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc
    intro s hs'
    have hsT : s ∈ Set.Icc (0:ℝ) T := by
      have h1 := Set.uIoc_subset_uIcc hs'
      rw [Set.uIcc_of_le hτpos] at h1
      exact ⟨h1.1, le_trans h1.2 hτ.2⟩
    obtain ⟨hprob, hys⟩ := pAlign_map_probSphere T hT μ0 hs Φ hΦ hsT
    haveI : IsProbabilityMeasure (μ0.map (Φ s)) := hprob
    have hintg : Integrable (fun x : Eucl d => x) (μ0.map (Φ s)) := by
      apply Integrable.mono' (integrable_const (μ := μ0.map (Φ s)) (1:ℝ)) aestronglyMeasurable_id
      filter_upwards [hys] with y hy
      simp only [sphere, Metric.mem_sphere, dist_zero_right] at hy
      simp [hy]
    exact norm_pAlign_field_le T hT (μ0.map (Φ s)) hys hintg
      (hΦ.sphere_bijOn s hsT |>.mapsTo hx)

/-- The Fundamental Theorem of Calculus representation of the flow along a `pAlign` trajectory. -/
theorem flow_sub_eq_integral (T : ℝ) (hT : 0 ≤ T) (μ0 : Measure (Eucl d)) [IsProbabilityMeasure μ0]
    (hs : μ0 (sphere d)ᶜ = 0)
    (Φ : ℝ → Eucl d → Eucl d) (hΦ : IsMeanFieldFlow (pAlign T hT) μ0 Φ)
    (x : Eucl d) (hx : x ∈ sphere d) {τ : ℝ} (hτ : τ ∈ Set.Icc (0:ℝ) T) :
    Φ τ x - x = ∫ s in (0:ℝ)..τ, (pAlign T hT).field (μ0.map (Φ s)) (Φ s x) := by
  have hderiv : ∀ s ∈ Set.uIcc (0:ℝ) τ, HasDerivAt (fun s => Φ s x)
      ((pAlign T hT).field (μ0.map (Φ s)) (Φ s x)) s := by
    intro s hs'
    have : s ∈ Set.Icc (0:ℝ) T := by
      rw [Set.uIcc_of_le hτ.1] at hs'
      exact ⟨hs'.1, le_trans hs'.2 hτ.2⟩
    exact hΦ.deriv x hx s (by simpa using this)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (intervalIntegrable_pAlign_field_traj T hT μ0 hs Φ hΦ x hx hτ)
  rw [hFTC, hΦ.init]
  simp

/-- The pointwise flow speed bound `‖Φ(τ,x) - x‖ ≤ τ` (the field has global norm `≤ 1`). -/
theorem norm_flow_sub_le (T : ℝ) (hT : 0 ≤ T) (μ0 : Measure (Eucl d)) [IsProbabilityMeasure μ0]
    (hs : μ0 (sphere d)ᶜ = 0)
    (Φ : ℝ → Eucl d → Eucl d) (hΦ : IsMeanFieldFlow (pAlign T hT) μ0 Φ)
    (x : Eucl d) (hx : x ∈ sphere d) {τ : ℝ} (hτ : τ ∈ Set.Icc (0:ℝ) T) :
    ‖Φ τ x - x‖ ≤ τ := by
  rw [flow_sub_eq_integral T hT μ0 hs Φ hΦ x hx hτ]
  have hb : ∀ s ∈ Set.uIcc (0:ℝ) τ, ‖(pAlign T hT).field (μ0.map (Φ s)) (Φ s x)‖ ≤ 1 := by
    intro s hs'
    have hsT : s ∈ Set.Icc (0:ℝ) T := by
      rw [Set.uIcc_of_le hτ.1] at hs'
      exact ⟨hs'.1, le_trans hs'.2 hτ.2⟩
    obtain ⟨hprob, hys⟩ := pAlign_map_probSphere T hT μ0 hs Φ hΦ hsT
    haveI := hprob
    have hintg : Integrable (fun x : Eucl d => x) (μ0.map (Φ s)) := by
      apply Integrable.mono' (integrable_const (μ := μ0.map (Φ s)) (1:ℝ)) aestronglyMeasurable_id
      filter_upwards [hys] with y hy
      simp only [sphere, Metric.mem_sphere, dist_zero_right] at hy
      simp [hy]
    exact norm_pAlign_field_le T hT (μ0.map (Φ s)) hys hintg (hΦ.sphere_bijOn s hsT |>.mapsTo hx)
  calc ‖∫ s in (0:ℝ)..τ, (pAlign T hT).field (μ0.map (Φ s)) (Φ s x)‖
      ≤ 1 * |τ - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro s hs'
        exact hb s (Set.uIoc_subset_uIcc hs')
    _ = τ := by rw [sub_zero, abs_of_nonneg hτ.1, one_mul]

/-- The barycenter of the pushforward is `τ`-Lipschitz-close to the original barycenter (the
pointwise flow speed bound, integrated against `μ0`). -/
theorem norm_barycenter_flow_sub_le (T : ℝ) (hT : 0 ≤ T) (μ0 : Measure (Eucl d))
    [IsProbabilityMeasure μ0] (hs : μ0 (sphere d)ᶜ = 0) (hint : Integrable (fun x : Eucl d => x) μ0)
    (Φ : ℝ → Eucl d → Eucl d) (hΦ : IsMeanFieldFlow (pAlign T hT) μ0 Φ)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0:ℝ) T) :
    ‖barycenter (μ0.map (Φ τ)) - barycenter μ0‖ ≤ τ := by
  have hmeas : Measurable (Φ τ) := hΦ.measurable τ (by simpa using hτ)
  have hintg2 : Integrable (fun y => Φ τ y) μ0 := by
    apply Integrable.mono' (integrable_const (2:ℝ)) (hmeas.aestronglyMeasurable)
    filter_upwards [hs] with y hy
    have hys : Φ τ y ∈ sphere d := (hΦ.sphere_bijOn τ (by simpa using hτ)).mapsTo hy
    simp only [sphere, Metric.mem_sphere, dist_zero_right] at hys
    rw [hys]; norm_num
  have heq : barycenter (μ0.map (Φ τ)) - barycenter μ0 = ∫ y, (Φ τ y - y) ∂μ0 := by
    have h1 : barycenter (μ0.map (Φ τ)) = ∫ y, Φ τ y ∂μ0 := by
      show ∫ y, y ∂(μ0.map (Φ τ)) = ∫ y, Φ τ y ∂μ0
      exact integral_map hmeas.aemeasurable aestronglyMeasurable_id
    rw [h1, barycenter, ← integral_sub hintg2 hint]
  rw [heq]
  calc ‖∫ y, (Φ τ y - y) ∂μ0‖ ≤ ∫ y, ‖Φ τ y - y‖ ∂μ0 := norm_integral_le_integral_norm _
    _ ≤ ∫ _y : Eucl d, τ ∂μ0 := by
        apply integral_mono_ae
        · exact (Integrable.sub hintg2 hint).norm
        · exact integrable_const τ
        · filter_upwards [hs] with y hy
          exact norm_flow_sub_le T hT μ0 hs Φ hΦ y hy hτ
    _ = τ := by simp

/-- **The uniform `O(τ²)` Taylor remainder bound** (Route 1′): the `pAlign` flow starting at any
`x` on the sphere agrees with the linear approximation `x + τ • P_x^⊥(E_{μ0}[x])` up to an error of
`3τ²`, UNIFORMLY over `x ∈ sphere d` (not merely for `x` in the topological support of `μ0`, and not
merely for `τ` small). The two `O(s)` terms driving the bound: the barycenter's own `O(s)`-drift
(`norm_barycenter_flow_sub_le`, via the projector's nonexpansiveness in `v`,
`norm_tangentialProjector_le`) and the trajectory's `O(s)`-drift composed with the projector's
base-point Lipschitz modulus (`norm_tangentialProjector_sub_point_le`, factor `2`). -/
theorem norm_taylor_remainder_le (T : ℝ) (hT : 0 ≤ T) (μ0 : Measure (Eucl d)) [IsProbabilityMeasure μ0]
    (hs : μ0 (sphere d)ᶜ = 0) (hint : Integrable (fun x : Eucl d => x) μ0)
    (Φ : ℝ → Eucl d → Eucl d) (hΦ : IsMeanFieldFlow (pAlign T hT) μ0 Φ)
    (x : Eucl d) (hx : x ∈ sphere d) {τ : ℝ} (hτ : τ ∈ Set.Icc (0:ℝ) T) :
    ‖Φ τ x - x - τ • tangentialProjector x (barycenter μ0)‖ ≤ 3 * τ ^ 2 := by
  have hτpos : 0 ≤ τ := hτ.1
  have hrepr : Φ τ x - x - τ • tangentialProjector x (barycenter μ0)
      = ∫ s in (0:ℝ)..τ, ((pAlign T hT).field (μ0.map (Φ s)) (Φ s x)
          - tangentialProjector x (barycenter μ0)) := by
    rw [flow_sub_eq_integral T hT μ0 hs Φ hΦ x hx hτ,
      intervalIntegral.integral_sub (intervalIntegrable_pAlign_field_traj T hT μ0 hs Φ hΦ x hx hτ)
        intervalIntegrable_const,
      intervalIntegral.integral_const, sub_zero]
  rw [hrepr]
  have hb : ∀ s ∈ Set.uIcc (0:ℝ) τ,
      ‖(pAlign T hT).field (μ0.map (Φ s)) (Φ s x) - tangentialProjector x (barycenter μ0)‖
        ≤ 3 * τ := by
    intro s hs'
    have hsIcc : s ∈ Set.Icc (0:ℝ) τ := by rwa [Set.uIcc_of_le hτpos] at hs'
    have hsT : s ∈ Set.Icc (0:ℝ) T := ⟨hsIcc.1, le_trans hsIcc.2 hτ.2⟩
    obtain ⟨hprob, hys⟩ := pAlign_map_probSphere T hT μ0 hs Φ hΦ hsT
    haveI := hprob
    have hΦsx : Φ s x ∈ sphere d := (hΦ.sphere_bijOn s hsT).mapsTo hx
    have heqf : (pAlign T hT).field (μ0.map (Φ s)) (Φ s x)
        = tangentialProjector (Φ s x) (barycenter (μ0.map (Φ s))) := pAlign_field T hT _ _
    rw [heqf]
    have hsplit : tangentialProjector (Φ s x) (barycenter (μ0.map (Φ s)))
        - tangentialProjector x (barycenter μ0)
        = (tangentialProjector (Φ s x) (barycenter (μ0.map (Φ s)))
            - tangentialProjector (Φ s x) (barycenter μ0))
          + (tangentialProjector (Φ s x) (barycenter μ0) - tangentialProjector x (barycenter μ0)) := by
      abel
    rw [hsplit]
    have hterm1 : ‖tangentialProjector (Φ s x) (barycenter (μ0.map (Φ s)))
        - tangentialProjector (Φ s x) (barycenter μ0)‖ ≤ s := by
      rw [tangentialProjector_sub_right]
      calc ‖tangentialProjector (Φ s x) (barycenter (μ0.map (Φ s)) - barycenter μ0)‖
          ≤ ‖barycenter (μ0.map (Φ s)) - barycenter μ0‖ := norm_tangentialProjector_le hΦsx _
        _ ≤ s := norm_barycenter_flow_sub_le T hT μ0 hs hint Φ hΦ hsT
    have hterm2 : ‖tangentialProjector (Φ s x) (barycenter μ0)
        - tangentialProjector x (barycenter μ0)‖ ≤ 2 * s := by
      calc ‖tangentialProjector (Φ s x) (barycenter μ0) - tangentialProjector x (barycenter μ0)‖
          ≤ 2 * ‖barycenter μ0‖ * ‖Φ s x - x‖ := norm_tangentialProjector_sub_point_le hΦsx hx _
        _ ≤ 2 * 1 * s := by
            gcongr
            · exact norm_barycenter_le_one hs hint
            · exact norm_flow_sub_le T hT μ0 hs Φ hΦ x hx hsT
        _ = 2 * s := by ring
    calc ‖(tangentialProjector (Φ s x) (barycenter (μ0.map (Φ s))) - tangentialProjector (Φ s x) (barycenter μ0))
          + (tangentialProjector (Φ s x) (barycenter μ0) - tangentialProjector x (barycenter μ0))‖
        ≤ s + 2 * s := norm_add_le_of_le hterm1 hterm2
      _ = 3 * s := by ring
      _ ≤ 3 * τ := by nlinarith [hsIcc.2]
  calc ‖∫ s in (0:ℝ)..τ, ((pAlign T hT).field (μ0.map (Φ s)) (Φ s x)
        - tangentialProjector x (barycenter μ0))‖
      ≤ (3 * τ) * |τ - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro s hs'
        exact hb s (Set.uIoc_subset_uIcc hs')
    _ = 3 * τ ^ 2 := by rw [sub_zero, abs_of_nonneg hτpos]; ring

end MeasureToMeasure.Leaves
