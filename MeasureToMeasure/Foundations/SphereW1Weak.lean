import MeasureToMeasure.Foundations.SphereProbMetric

/-!
# `W₁` vs weak convergence on `SphereProb`: the easy direction (M3b existence, leaf S3a)

The crux of the Wasserstein completeness sub-campaign (toward `exists_meanFieldFlow`) is that the `W₁`
pseudometric on `SphereProb d` (leaf S2) is uniformly equivalent to the Lévy–Prokhorov / weak metric
banked complete in `SphereMeasureCompletion` (E1). This file records the **easy** half — `W₁` dominates
weak convergence — via Kantorovich–Rubinstein.

* `SphereProb.integrable_of_lipschitz` — a globally `1`-Lipschitz `f : Eucl d → ℝ` is integrable
  against a sphere-supported probability measure (bounded on the sphere ⇒ a.e.-bounded ⇒ integrable);
* `SphereProb.abs_integral_sub_le_dist` — for such `f`, `|∫ f dμ − ∫ f dν| ≤ dist μ ν`, the banked KR
  lower bound `ofReal_integral_sub_le_W1` read through `toReal` (finite by S2a) and symmetrised.

This is the tool that makes `id : (SphereProb, W₁) → (P(sphere), weak)` continuous: `W₁`-convergence
forces integral-convergence against every Lipschitz test function, and on the compact sphere Lipschitz
functions determine weak convergence. The **hard** direction (weak ⇒ `W₁`) and the completeness
transport are the following leaves (S3b/S4).

M3b staging: consumed when `exists_meanFieldFlow` is discharged; see RESEARCH.md.
-/

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace MeasureToMeasure

variable {d : ℕ}

namespace SphereProb

/-- A globally `1`-Lipschitz `f : Eucl d → ℝ` is integrable against a sphere-supported probability
measure: on the sphere `‖x‖ = 1`, so `|f x| ≤ |f 0| + 1` a.e., a constant bound on a finite measure. -/
theorem integrable_of_lipschitz {f : Eucl d → ℝ} (hf : LipschitzWith 1 f) (μ : SphereProb d) :
    Integrable f μ.val := by
  haveI := μ.property.1
  have hbound : ∀ᵐ x ∂μ.val, ‖f x‖ ≤ |f 0| + 1 := by
    filter_upwards [ae_norm_le_one_of_sphere_supported μ.property.2] with x hx
    have hlip : |f x - f 0| ≤ ‖x‖ := by
      have h := hf.dist_le_mul x 0
      rw [Real.dist_eq, dist_zero_right, NNReal.coe_one, one_mul] at h
      exact h
    calc ‖f x‖ = |f x| := Real.norm_eq_abs _
      _ ≤ |f 0| + |f x - f 0| := by linarith [abs_sub_abs_le_abs_sub (f x) (f 0)]
      _ ≤ |f 0| + ‖x‖ := by linarith
      _ ≤ |f 0| + 1 := by linarith
  exact Integrable.mono' (integrable_const (|f 0| + 1)) hf.continuous.aestronglyMeasurable hbound

/-- **Kantorovich–Rubinstein estimate on `SphereProb` (easy direction of the `W₁ ↔ weak` comparison).**
For a globally `1`-Lipschitz test function `f`, the difference of integrals is bounded by the `W₁`
distance: `|∫ f dμ − ∫ f dν| ≤ dist μ ν`. This is the banked KR lower bound `ofReal_integral_sub_le_W1`
symmetrised and read through `toReal` (finite by S2a); it makes `id : (SphereProb, W₁) → (P(sphere),
weak)` continuous (Lipschitz test functions determine weak convergence). -/
theorem abs_integral_sub_le_dist {f : Eucl d → ℝ} (hf : LipschitzWith 1 f) (μ ν : SphereProb d) :
    |∫ x, f x ∂μ.val - ∫ x, f x ∂ν.val| ≤ dist μ ν := by
  haveI := μ.property.1
  haveI := ν.property.1
  have hne : W1 μ.val ν.val ≠ ⊤ := w1dist_ne_top μ ν
  have hne' : W1 ν.val μ.val ≠ ⊤ := w1dist_ne_top ν μ
  have hμ := integrable_of_lipschitz hf μ
  have hν := integrable_of_lipschitz hf ν
  -- forward: ∫f dμ - ∫f dν ≤ dist μ ν
  have h1 : ∫ x, f x ∂μ.val - ∫ x, f x ∂ν.val ≤ dist μ ν := by
    rw [dist_eq]
    rw [← ENNReal.ofReal_le_iff_le_toReal hne]
    exact ofReal_integral_sub_le_W1 hf hμ hν
  -- backward: ∫f dν - ∫f dμ ≤ dist μ ν  (swap, then W1_comm)
  have h2 : ∫ x, f x ∂ν.val - ∫ x, f x ∂μ.val ≤ dist μ ν := by
    rw [dist_eq, W1_comm]
    rw [← ENNReal.ofReal_le_iff_le_toReal hne']
    exact ofReal_integral_sub_le_W1 hf hν hμ
  rw [abs_sub_le_iff]
  exact ⟨h1, h2⟩

end SphereProb

end MeasureToMeasure
