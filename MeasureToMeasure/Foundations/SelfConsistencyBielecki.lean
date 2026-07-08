import MeasureToMeasure.Foundations.SelfConsistencyGronwall
import MeasureToMeasure.Foundations.BieleckiMetricSpace
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The genuine McKean-Vlasov contraction estimate, via a from-scratch variable-forcing Grönwall
(M3b existence, leaf E3l)

Leaf E3k banked a Grönwall bound comparing `trajectoryFlow p hT η₁ x` and
`trajectoryFlow p hT η₂ x` for two arbitrary trial trajectories, but flagged it as NOT the genuine
contraction: the forcing term used the ambient sup-metric `dist η₁ η₂`, giving an exponential bound
with no Bielecki reweighting anywhere. This leaf closes that gap by keeping the pointwise forcing
`dist (η₁ s) (η₂ s) ≤ e^{λs}·bieleckiDist η₁ η₂` genuinely *inside* the comparison argument, via a
**variable-forcing Grönwall lemma built from scratch** (`gronwall_variable_forcing`):

  `h' ≤ K·h + G·e^{λt}`, `h(0) ≤ 0`, `K < λ` implies `h(t) ≤ (G/(λ-K))·(e^{λt} - e^{Kt})`.

Mathlib's `Analysis/ODE/Gronwall.lean` only provides the CONSTANT-forcing corollary
(`norm_le_gronwallBound_of_norm_deriv_right_le`); the TODO note in that file explicitly flags the
variable-forcing generalization as future work. This leaf supplies exactly that generalization,
proved directly from the underlying one-dimensional fencing machinery in
`Analysis/Calculus/MeanValue.lean` (`image_le_of_liminf_slope_right_lt_deriv_boundary`), mirroring
the ε-perturbation ("strict fencing for `C' > C`, then take `C' → C⁺` via `closure_le`") trick
Mathlib's own `gronwallBound`-based lemmas use internally.

Applying it to `h(t) := dist (trajectoryFlow p hT η₁ x t) (trajectoryFlow p hT η₂ x t)` (via
`HasDerivWithinAt.liminf_right_slope_norm_le` to get the needed liminf-slope bound from the FTC
derivative, exactly as leaf E3k's field-difference bound feeds it, but keeping the Bielecki-bounded
`dist (η₁ s) (η₂ s)` term as a genuine FUNCTION of `s` rather than maxing it to a constant first)
gives `dist_trajectoryFlow_sub_le_bielecki`:

  `dist (trajFlow η₁ x t) (trajFlow η₂ x t) ≤ (2M·bieleckiDist η₁ η₂ / (λ-K)) · (e^{λt} - e^{Kt})`

-- exactly the closed-form Duhamel estimate the campaign memory predicted, with `K` the field's
point-Lipschitz constant and `M` its measure-Lipschitz constant (both from leaf E3c). Choosing
`λ > K + 2M` will make the coefficient `2M/(λ-K) < 1`, giving the genuine contraction once this is
transferred to the pushforward/Bielecki-metric level (the next leaf).

M3b staging: consumed when `exists_meanFieldFlow` is discharged; see RESEARCH.md.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal Topology

namespace MeasureToMeasure.Foundations

variable {d : ℕ}

/-- **Variable-forcing Grönwall (`-- ForMathlib candidate:`, generalizes the TODO note in
`Analysis/ODE/Gronwall.lean`).** If `h ≥ 0` is continuous on `[0,T]` with `h(0) ≤ 0` and its
right-derivative liminf-slope is bounded by `K·h(t) + G·e^{λt}` (`K < λ`), then `h(t) ≤
(G/(λ-K))·(e^{λt} - e^{Kt})`. Proved by the strict-fencing-then-limit trick: for every `C' > G/(λ-K)`,
`B(t) := C'·(e^{λt}-e^{Kt})` strictly dominates the forcing at every touching point, so
`image_le_of_liminf_slope_right_lt_deriv_boundary` gives `h ≤ B`; then `C' → G/(λ-K)⁺` via
`ContinuousWithinAt.closure_le`. -/
theorem gronwall_variable_forcing {T K lam G : ℝ} (hlamK : K < lam)
    (h : ℝ → ℝ) (hcont : ContinuousOn h (Icc (0:ℝ) T))
    (hliminf : ∀ x ∈ Ico (0:ℝ) T, ∀ r, K * h x + G * Real.exp (lam * x) < r →
      ∃ᶠ z in 𝓝[>] x, (z - x)⁻¹ * (h z - h x) < r)
    (h0 : h 0 ≤ 0) :
    ∀ x ∈ Icc (0:ℝ) T, h x ≤ (G / (lam - K)) * (Real.exp (lam * x) - Real.exp (K * x)) := by
  have hlamKpos : 0 < lam - K := by linarith
  have H : ∀ x ∈ Icc (0:ℝ) T, ∀ C' ∈ Ioi (G / (lam - K)),
      h x ≤ C' * (Real.exp (lam * x) - Real.exp (K * x)) := by
    intro x hx C' hC'
    rw [Set.mem_Ioi] at hC'
    have hBderiv : ∀ t : ℝ, HasDerivAt (fun t => C' * (Real.exp (lam * t) - Real.exp (K * t)))
        (C' * (lam * Real.exp (lam * t) - K * Real.exp (K * t))) t := by
      intro t
      have h1 : HasDerivAt (fun t => Real.exp (lam * t)) (lam * Real.exp (lam * t)) t := by
        have hderiv : HasDerivAt (fun t : ℝ => lam * t) lam t := by
          simpa using (hasDerivAt_id t).const_mul lam
        simpa [mul_comm] using hderiv.exp
      have h2 : HasDerivAt (fun t => Real.exp (K * t)) (K * Real.exp (K * t)) t := by
        have hderiv : HasDerivAt (fun t : ℝ => K * t) K t := by
          simpa using (hasDerivAt_id t).const_mul K
        simpa [mul_comm] using hderiv.exp
      exact (h1.sub h2).const_mul C'
    apply image_le_of_liminf_slope_right_lt_deriv_boundary hcont hliminf
    · show h 0 ≤ C' * (Real.exp (lam * 0) - Real.exp (K * 0))
      simp; linarith
    · exact hBderiv
    · intro t ht heq
      have key : G < C' * (lam - K) := by
        rw [div_lt_iff₀ hlamKpos] at hC'
        linarith [hC']
      rw [heq]
      show K * (C' * (Real.exp (lam * t) - Real.exp (K * t))) + G * Real.exp (lam * t)
        < C' * (lam * Real.exp (lam*t) - K * Real.exp (K*t))
      nlinarith [Real.exp_pos (lam * t), key]
    · exact hx
  intro x hx
  have Hlim : ∀ C' ∈ closure (Ioi (G / (lam - K))),
      h x ≤ C' * (Real.exp (lam * x) - Real.exp (K * x)) := by
    intro C' hC'
    have hcontC : ContinuousWithinAt (fun c => c * (Real.exp (lam * x) - Real.exp (K * x)))
        (Ioi (G / (lam - K))) C' :=
      Continuous.continuousWithinAt (continuous_id.mul continuous_const)
    have hge : ContinuousWithinAt (fun _ : ℝ => h x) (Ioi (G / (lam - K))) C' := continuousWithinAt_const
    exact hge.closure_le hC' hcontC (fun c hc => H x hx c hc)
  rw [closure_Ioi] at Hlim
  exact Hlim (G / (lam - K)) Set.self_mem_Ici

/-- Pointwise form of `bieleckiDist`'s domination bound: `dist (η₁ s) (η₂ s) ≤ e^{λs}·bieleckiDist
η₁ η₂`, the same bound `dist_le_exp_mul_bieleckiDist` (leaf E3a) gives for the whole trajectory,
evaluated at a single time `s`. -/
theorem dist_le_exp_mul_bieleckiDist_pointwise' {T lam : ℝ} (hlam : 0 ≤ lam)
    (η₁ η₂ : C(Set.Icc (0:ℝ) T, SphereProb d)) (s : Set.Icc (0:ℝ) T) :
    dist (η₁ s) (η₂ s) ≤ Real.exp (lam * s.1) * bieleckiDist (T := T) (lam := lam) η₁ η₂ := by
  have := le_bieleckiDist (T := T) (lam := lam) hlam η₁ η₂ s
  unfold bieleckiWeight at this
  rw [neg_mul] at this
  calc dist (η₁ s) (η₂ s)
      = (Real.exp (-(lam * s.1)))⁻¹ * (Real.exp (-(lam * s.1)) * dist (η₁ s) (η₂ s)) := by
        field_simp
    _ ≤ (Real.exp (-(lam * s.1)))⁻¹ * bieleckiDist (T := T) (lam := lam) η₁ η₂ := by gcongr
    _ = Real.exp (lam * s.1) * bieleckiDist (T := T) (lam := lam) η₁ η₂ := by
        rw [← Real.exp_neg, neg_neg]

/-- **The genuine McKean-Vlasov contraction estimate (pointwise).** Applying
`gronwall_variable_forcing` to `h(t) := dist (trajectoryFlow p hT η₁ x t)
(trajectoryFlow p hT η₂ x t)`: its right-derivative liminf-slope is bounded by `K·h(t) +
G·e^{λt}` (`K` the point-Lipschitz constant, `G` built from the measure-Lipschitz constant `M`
times `bieleckiDist η₁ η₂`, leaf E3c's joint modulus split exactly as in leaf E3k, but keeping the
Bielecki-bounded pointwise forcing term intact rather than maxing it to a constant). This gives the
closed-form Duhamel bound with a genuine `bieleckiDist` factor, the ingredient the outer
self-consistency contraction (next leaf) needs. -/
theorem dist_trajectoryFlow_sub_le_bielecki (p : AttnParams d) {T lam : ℝ} (hT : 0 ≤ T)
    (hlam : 0 ≤ lam)
    (η₁ η₂ : C(Set.Icc (0:ℝ) T, SphereProb d)) {x : Eucl d} (hx : x ∈ sphere d)
    (hlamK : ((Real.toNNReal (5 * fieldBallLip p + 4 * fieldBallBound p)
      + Real.toNNReal (5 * fieldBallBound p) : ℝ≥0) : ℝ) < lam) :
    ∀ t ∈ Set.Icc (0:ℝ) T,
      dist (trajectoryFlow p hT η₁ x t) (trajectoryFlow p hT η₂ x t) ≤
        (2 * (‖p.V‖ * ((Real.exp (2 * ‖p.B‖) + Real.exp (4 * ‖p.B‖)) * (1 + ‖p.B‖))) *
          bieleckiDist (T := T) (lam := lam) η₁ η₂ /
          (lam - ((Real.toNNReal (5 * fieldBallLip p + 4 * fieldBallBound p)
            + Real.toNNReal (5 * fieldBallBound p) : ℝ≥0) : ℝ))) *
        (Real.exp (lam * t) - Real.exp
          (((Real.toNNReal (5 * fieldBallLip p + 4 * fieldBallBound p)
            + Real.toNNReal (5 * fieldBallBound p) : ℝ≥0) : ℝ) * t)) := by
  set K : ℝ := ((Real.toNNReal (5 * fieldBallLip p + 4 * fieldBallBound p)
    + Real.toNNReal (5 * fieldBallBound p) : ℝ≥0) : ℝ) with hK
  set G : ℝ := 2 * (‖p.V‖ * ((Real.exp (2 * ‖p.B‖) + Real.exp (4 * ‖p.B‖)) * (1 + ‖p.B‖)))
    * bieleckiDist (T := T) (lam := lam) η₁ η₂ with hG
  set f : ℝ → Eucl d := fun t => trajectoryFlow p hT η₁ x t - trajectoryFlow p hT η₂ x t with hf
  set h : ℝ → ℝ := fun t => ‖f t‖ with hh
  have hfcont : ContinuousOn f (Set.Icc (0:ℝ) T) := by
    rw [hf]
    exact (continuousOn_trajectoryFlow p hT η₁ hx).sub (continuousOn_trajectoryFlow p hT η₂ hx)
  have hhcont : ContinuousOn h (Set.Icc (0:ℝ) T) := by
    rw [hh]; exact continuous_norm.comp_continuousOn hfcont
  have hfderiv : ∀ s ∈ Set.Ico (0:ℝ) T, HasDerivWithinAt f
      (trajectoryField p hT η₁ s (trajectoryFlow p hT η₁ x s)
        - trajectoryField p hT η₂ s (trajectoryFlow p hT η₂ x s)) (Set.Ici s) s := by
    intro s hs
    have h1 := hasDerivWithinAt_trajectoryFlow p hT η₁ hx (Set.Ico_subset_Icc_self hs)
    have h2 := hasDerivWithinAt_trajectoryFlow p hT η₂ hx (Set.Ico_subset_Icc_self hs)
    have h1' := h1.mono_of_mem_nhdsWithin (icc_mem_nhdsWithin_ici hs)
    have h2' := h2.mono_of_mem_nhdsWithin (icc_mem_nhdsWithin_ici hs)
    exact h1'.sub h2'
  have hderivbound : ∀ s ∈ Set.Ico (0:ℝ) T,
      ‖trajectoryField p hT η₁ s (trajectoryFlow p hT η₁ x s)
        - trajectoryField p hT η₂ s (trajectoryFlow p hT η₂ x s)‖ ≤
      K * h s + G * Real.exp (lam * s) := by
    intro s hs
    have hproj_eq : Set.projIcc 0 T hT s = ⟨s, Set.Ico_subset_Icc_self hs⟩ :=
      Set.projIcc_of_mem hT (Set.Ico_subset_Icc_self hs)
    unfold trajectoryField
    rw [hproj_eq]
    haveI hp1 := (η₁ (⟨s, Set.Ico_subset_Icc_self hs⟩ : Set.Icc (0:ℝ) T)).property.1
    haveI hp2 := (η₂ (⟨s, Set.Ico_subset_Icc_self hs⟩ : Set.Icc (0:ℝ) T)).property.1
    have hxsphere2 : trajectoryFlow p hT η₂ x s ∈ sphere d :=
      trajectoryFlow_mem_sphere p hT η₂ hx (Set.Ico_subset_Icc_self hs)
    have hxnorm2 : ‖trajectoryFlow p hT η₂ x s‖ = 1 := norm_eq_one_of_mem_sphere hxsphere2
    have hW1ne : W1 (η₁ (⟨s, Set.Ico_subset_Icc_self hs⟩ : Set.Icc (0:ℝ) T)).val
        (η₂ (⟨s, Set.Ico_subset_Icc_self hs⟩ : Set.Icc (0:ℝ) T)).val ≠ ⊤ :=
      SphereProb.w1dist_ne_top _ _
    have hle_measure := norm_attnFieldExt_sub_measure_le p
      (η₁ (⟨s, Set.Ico_subset_Icc_self hs⟩ : Set.Icc (0:ℝ) T)).property.2
      (η₂ (⟨s, Set.Ico_subset_Icc_self hs⟩ : Set.Icc (0:ℝ) T)).property.2 hW1ne
      (trajectoryFlow p hT η₂ x s)
    have hWeq : (W1 (η₁ (⟨s, Set.Ico_subset_Icc_self hs⟩ : Set.Icc (0:ℝ) T)).val
          (η₂ (⟨s, Set.Ico_subset_Icc_self hs⟩ : Set.Icc (0:ℝ) T)).val).toReal
        = dist (η₁ (⟨s, Set.Ico_subset_Icc_self hs⟩ : Set.Icc (0:ℝ) T))
            (η₂ (⟨s, Set.Ico_subset_Icc_self hs⟩ : Set.Icc (0:ℝ) T)) := (SphereProb.dist_eq _ _).symm
    rw [hWeq, hxnorm2] at hle_measure
    norm_num at hle_measure
    have hle_bielecki := dist_le_exp_mul_bieleckiDist_pointwise' (T := T) (lam := lam) hlam η₁ η₂
      ⟨s, Set.Ico_subset_Icc_self hs⟩
    simp only at hle_bielecki
    have hfeq : ‖trajectoryFlow p hT η₁ x s - trajectoryFlow p hT η₂ x s‖ = h s := by rw [hh, hf]
    have hstep : 2 * (‖p.V‖ * ((Real.exp (2 * ‖p.B‖) + Real.exp (4 * ‖p.B‖)) * (1 + ‖p.B‖))
        * dist (η₁ (⟨s, Set.Ico_subset_Icc_self hs⟩ : Set.Icc (0:ℝ) T))
            (η₂ ⟨s, Set.Ico_subset_Icc_self hs⟩))
        ≤ G * Real.exp (lam * s) := by
      rw [hG]
      calc 2 * (‖p.V‖ * ((Real.exp (2 * ‖p.B‖) + Real.exp (4 * ‖p.B‖)) * (1 + ‖p.B‖))
            * dist (η₁ (⟨s, Set.Ico_subset_Icc_self hs⟩ : Set.Icc (0:ℝ) T))
                (η₂ ⟨s, Set.Ico_subset_Icc_self hs⟩))
          ≤ 2 * (‖p.V‖ * ((Real.exp (2 * ‖p.B‖) + Real.exp (4 * ‖p.B‖)) * (1 + ‖p.B‖))
              * (Real.exp (lam * s) * bieleckiDist (T := T) (lam := lam) η₁ η₂)) := by gcongr
        _ = 2 * (‖p.V‖ * ((Real.exp (2 * ‖p.B‖) + Real.exp (4 * ‖p.B‖)) * (1 + ‖p.B‖)))
              * bieleckiDist (T := T) (lam := lam) η₁ η₂ * Real.exp (lam * s) := by ring
    calc ‖attnFieldExt p (η₁ (⟨s, Set.Ico_subset_Icc_self hs⟩ : Set.Icc (0:ℝ) T)).val
            (trajectoryFlow p hT η₁ x s)
          - attnFieldExt p (η₂ (⟨s, Set.Ico_subset_Icc_self hs⟩ : Set.Icc (0:ℝ) T)).val
            (trajectoryFlow p hT η₂ x s)‖
        ≤ ‖attnFieldExt p (η₁ (⟨s, Set.Ico_subset_Icc_self hs⟩ : Set.Icc (0:ℝ) T)).val
              (trajectoryFlow p hT η₁ x s)
            - attnFieldExt p (η₁ (⟨s, Set.Ico_subset_Icc_self hs⟩ : Set.Icc (0:ℝ) T)).val
              (trajectoryFlow p hT η₂ x s)‖
          + ‖attnFieldExt p (η₁ (⟨s, Set.Ico_subset_Icc_self hs⟩ : Set.Icc (0:ℝ) T)).val
              (trajectoryFlow p hT η₂ x s)
            - attnFieldExt p (η₂ (⟨s, Set.Ico_subset_Icc_self hs⟩ : Set.Icc (0:ℝ) T)).val
              (trajectoryFlow p hT η₂ x s)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ K * ‖trajectoryFlow p hT η₁ x s - trajectoryFlow p hT η₂ x s‖
          + 2 * (‖p.V‖ * ((Real.exp (2 * ‖p.B‖) + Real.exp (4 * ‖p.B‖)) * (1 + ‖p.B‖))
            * dist (η₁ (⟨s, Set.Ico_subset_Icc_self hs⟩ : Set.Icc (0:ℝ) T))
                (η₂ ⟨s, Set.Ico_subset_Icc_self hs⟩)) :=
        add_le_add
          (by rw [hK, ← dist_eq_norm, ← dist_eq_norm]
              exact (attnFieldExt_lipschitz p (η₁ ⟨s, Set.Ico_subset_Icc_self hs⟩).val
                (η₁ ⟨s, Set.Ico_subset_Icc_self hs⟩).property.2).dist_le_mul
                (trajectoryFlow p hT η₁ x s) (trajectoryFlow p hT η₂ x s))
          hle_measure
      _ ≤ K * h s + G * Real.exp (lam * s) := by
          rw [hfeq]
          exact add_le_add le_rfl hstep
  have hliminf : ∀ s ∈ Set.Ico (0:ℝ) T, ∀ r, K * h s + G * Real.exp (lam * s) < r →
      ∃ᶠ z in 𝓝[>] s, (z - s)⁻¹ * (h z - h s) < r := by
    intro s hs r hr
    have hlt : ‖trajectoryField p hT η₁ s (trajectoryFlow p hT η₁ x s)
        - trajectoryField p hT η₂ s (trajectoryFlow p hT η₂ x s)‖ < r :=
      lt_of_le_of_lt (hderivbound s hs) hr
    have hslope := (hfderiv s hs).liminf_right_slope_norm_le hlt
    rwa [hh]
  have hh0 : h 0 ≤ 0 := by
    rw [hh, hf]
    simp [trajectoryFlow_zero p hT η₁ hx, trajectoryFlow_zero p hT η₂ hx]
  have hfinal := gronwall_variable_forcing hlamK h hhcont hliminf hh0
  intro t ht
  have h' := hfinal t ht
  simp only [hh, hf] at h'
  rwa [dist_eq_norm]

end MeasureToMeasure.Foundations
