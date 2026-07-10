import MeasureToMeasure.Foundations.Sphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Order.IntermediateValue

/-!
# Spherical slabs are connected, for `d ≥ 3` (Proposition 2.2, Step C)

The last geometric ingredient for `prop_2_2`'s connected-prescribed-mass partition: given the
generic direction `u` (Step A, `AtomlessDirection.lean`) and thresholds `a ≤ b` (Step B,
`ThresholdExtraction.lean`), the slab `{x ∈ sphere d | a ≤ ⟪u,x⟫ ≤ b}` is a connected subset of the
sphere. This is exactly what a Sierpiński-only mass-carving construction *cannot* offer (a bare
measurable partition generically has no topological structure), and exactly what the paper's
downstream gated-perceptron routing needs (a piece that can be swept as one connected region).

**The construction.** Let `K := (⟪u,·⟩)⁻¹(0)`, the orthogonal complement of `u` (a `(d-1)`-dimensional
subspace). The map `Ψ(ω,t) := t•u + √(1-t²)•ω`, restricted to `{ω ∈ K | ‖ω‖=1} × [a,b]`, is
continuous and lands exactly on the slab: `‖Ψ(ω,t)‖=1` and `⟪u,Ψ(ω,t)⟫=t` are algebraic identities
using only `ω ⊥ u`, `‖u‖=‖ω‖=1` (`Eucl.norm_eq_one_of_mem_sphere`-style Pythagorean computation).
It is *surjective* onto the slab (`exists_omega_apply`): given `x` in the slab, `t:=⟪u,x⟫` and
`y:=x-t•u` satisfy `‖y‖²=1-t²` unconditionally, so `ω:=y/‖y‖` (or an arbitrary fallback unit vector
of `K` when `y=0`, i.e. exactly at the poles `t=±1`) recovers `x = Ψ(ω,t)`.

Since `{ω ∈ K | ‖ω‖=1}` (an `S^{d-2}`) is connected exactly when `1 < Module.rank ℝ K`, i.e.
`dim K = d - 1 ≥ 2`, i.e. `d ≥ 3` (`isConnected_sphere`, applied to the submodule `K` treated as its
own normed space and pushed forward along its continuous inclusion into `Eucl d`), and `[a,b]` is
always connected, the domain `{ω∈K|‖ω‖=1} × [a,b]` is connected (`IsConnected.prod`) -- so its
continuous, surjective image, the slab, is connected too.

This is the same recurring `d ≥ 3` threshold seen throughout this campaign (routing room on the
linear layer, `prop_4_2`'s anchor construction) -- here it is exactly "`S^{d-2}` is connected".

M3b/mid-level staging: Step C of the `prop_2_2` partition construction; see `Statements/MidLevel.lean`.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Set
open scoped RealInnerProductSpace
open MeasureToMeasure

variable {d : ℕ}

/-- **The residual `x - ⟪u,x⟫•u` has squared norm `1-⟪u,x⟫²`, unconditionally** (Pythagorean
decomposition of a unit vector along `u`, no case split on whether `⟪u,x⟫=±1`). -/
theorem norm_sub_proj_sq (u : Metric.sphere (0:Eucl d) 1) (x : Eucl d) (hxnorm : ‖x‖ = 1) :
    ‖x - (⟪(u:Eucl d), x⟫:ℝ) • (u:Eucl d)‖^2 = 1 - (⟪(u:Eucl d), x⟫:ℝ)^2 := by
  have hun : ‖(u:Eucl d)‖ = 1 := by
    have := u.2; rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at this; exact this
  rw [norm_sub_sq_real, norm_smul, hxnorm, real_inner_comm x, real_inner_smul_right, hun,
    Real.norm_eq_abs]
  nlinarith [sq_abs (⟪x, (u:Eucl d)⟫ : ℝ)]

/-- **Surjectivity of the `Ψ`-parametrization**: every unit `x` is `Ψ ω ⟪u,x⟫` for some unit
`ω ⊥ u`. The construction is uniform across the poles: `ω := ‖y‖⁻¹•y` where `y:=x-⟪u,x⟫•u` when
`y ≠ 0`, and an arbitrary fallback unit vector of `K` (needs `K` nontrivial, i.e. `finrank K ≥ 1`)
when `y = 0` (exactly `x = ±u`, where `Ψ`'s value doesn't depend on `ω` since its coefficient
`√(1-t²)` vanishes there too). -/
theorem exists_omega_apply (u : Metric.sphere (0:Eucl d) 1) (hK : 1 ≤ Module.finrank ℝ
      (((innerSL ℝ (u:Eucl d) : Eucl d →L[ℝ] ℝ) : Eucl d →ₗ[ℝ] ℝ).ker))
    (x : Eucl d) (hxnorm : ‖x‖ = 1) :
    ∃ ω : Eucl d, ω ∈ ((innerSL ℝ (u:Eucl d) : Eucl d →L[ℝ] ℝ) : Eucl d →ₗ[ℝ] ℝ).ker ∧ ‖ω‖ = 1 ∧
      (⟪(u:Eucl d), x⟫:ℝ) • (u:Eucl d) + Real.sqrt (1 - (⟪(u:Eucl d), x⟫:ℝ)^2) • ω = x := by
  set K := ((innerSL ℝ (u:Eucl d) : Eucl d →L[ℝ] ℝ) : Eucl d →ₗ[ℝ] ℝ).ker with hKdef
  set t := (⟪(u:Eucl d), x⟫ : ℝ) with htdef
  set y := x - t • (u:Eucl d) with hydef
  have hun : ‖(u:Eucl d)‖ = 1 := by
    have := u.2; rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at this; exact this
  have hyK : y ∈ K := by
    rw [hKdef, hydef, LinearMap.mem_ker]
    show (⟪(u:Eucl d), x - t • (u:Eucl d)⟫ : ℝ) = 0
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hun, htdef]
    ring
  have hynormsq : ‖y‖^2 = 1 - t^2 := by rw [hydef, htdef]; exact norm_sub_proj_sq u x hxnorm
  obtain ⟨ω₀, hω₀K, hω₀norm⟩ : ∃ ω : Eucl d, ω ∈ K ∧ ‖ω‖ = 1 := by
    have hne : K ≠ ⊥ := by
      intro hcon; rw [hcon] at hK; simp at hK
    obtain ⟨v, hvK, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact ⟨‖v‖⁻¹ • v, K.smul_mem _ hvK, by rw [norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]⟩
  by_cases hy0 : y = 0
  · refine ⟨ω₀, hω₀K, hω₀norm, ?_⟩
    have ht2 : t^2 = 1 := by
      have hz : ‖y‖^2 = 0 := by rw [hy0]; simp
      rw [hz] at hynormsq; linarith
    have hxeq : x - t • (u:Eucl d) = 0 := hydef.symm.trans hy0
    rw [show (1:ℝ) - t^2 = 0 from by linarith, Real.sqrt_zero, zero_smul, add_zero]
    exact (eq_of_sub_eq_zero hxeq).symm
  · refine ⟨‖y‖⁻¹ • y, K.smul_mem _ hyK, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy0)]
    · have hynn : (0:ℝ) ≤ ‖y‖ := norm_nonneg y
      have hsqrty : Real.sqrt (1 - t^2) = ‖y‖ := by
        rw [← hynormsq, Real.sqrt_sq hynn]
      rw [hsqrty, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy0), one_smul, hydef]
      module

/-- **The unit sphere of a submodule, as a subset of the ambient space, is connected** whenever
the submodule's rank exceeds `1`: push `isConnected_sphere` (about the submodule's own type)
forward along its continuous inclusion into the ambient space. -/
theorem isConnected_sphere_submodule (K : Submodule ℝ (Eucl d)) (h : 1 < Module.rank ℝ K) :
    IsConnected {x : Eucl d | x ∈ K ∧ ‖x‖ = 1} := by
  have hconn : IsConnected (Metric.sphere (0 : K) 1) := isConnected_sphere h 0 (by norm_num)
  have hcont : Continuous (K.subtype) := K.subtype.continuous_of_finiteDimensional
  have himg : (K.subtype) '' (Metric.sphere (0 : K) 1) = {x : Eucl d | x ∈ K ∧ ‖x‖ = 1} := by
    ext x
    simp only [Set.mem_image, Metric.mem_sphere, dist_eq_norm, sub_zero, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      show ‖(y:Eucl d)‖ = 1
      exact hy
    · rintro ⟨hxK, hxnorm⟩
      refine ⟨⟨x, hxK⟩, ?_, rfl⟩
      show ‖x‖ = 1
      exact hxnorm
  rw [← himg]
  exact hconn.image K.subtype hcont.continuousOn

/-- **A spherical slab is connected, for `d ≥ 3`.** The `Ψ`-parametrization is a continuous
surjection from `{ω ∈ u^⊥ | ‖ω‖=1} × [a,b]` (connected, since `S^{d-2}` is connected for `d≥3`)
onto the slab `{x ∈ sphere d | a ≤ ⟪u,x⟫ ≤ b}` -- so the slab, as a continuous image of a connected
set, is connected. -/
theorem isConnected_slab (u : Metric.sphere (0:Eucl d) 1) (hd : 3 ≤ d)
    (a b : ℝ) (hab : a ≤ b) (haneg1 : -1 ≤ a) (hb1 : b ≤ 1) :
    IsConnected {x : Eucl d | x ∈ sphere d ∧ a ≤ (⟪(u:Eucl d), x⟫:ℝ) ∧ (⟪(u:Eucl d), x⟫:ℝ) ≤ b} := by
  set K := ((innerSL ℝ (u:Eucl d) : Eucl d →L[ℝ] ℝ) : Eucl d →ₗ[ℝ] ℝ).ker with hKdef
  have hfinK : Module.finrank ℝ K = d - 1 := by
    have hrange : LinearMap.range ((innerSL ℝ (u:Eucl d) : Eucl d →L[ℝ] ℝ) : Eucl d →ₗ[ℝ] ℝ) = ⊤ := by
      rw [Submodule.eq_top_iff']
      intro y
      refine ⟨(y / ‖(u:Eucl d)‖^2) • (u:Eucl d), ?_⟩
      show (⟪(u:Eucl d), (y/‖(u:Eucl d)‖^2) • (u:Eucl d)⟫ : ℝ) = y
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    have hrankeq := LinearMap.finrank_range_add_finrank_ker
      ((innerSL ℝ (u:Eucl d) : Eucl d →L[ℝ] ℝ) : Eucl d →ₗ[ℝ] ℝ)
    rw [hrange, ← hKdef] at hrankeq
    simp only [finrank_top] at hrankeq
    have hfineucl : Module.finrank ℝ (Eucl d) = d := finrank_euclideanSpace_fin
    rw [hfineucl] at hrankeq
    have hfinR : Module.finrank ℝ ℝ = 1 := Module.finrank_self ℝ
    rw [hfinR] at hrankeq
    omega
  have hrankK : 1 < Module.rank ℝ K := by
    rw [← Module.finrank_eq_rank, hfinK]
    have : (2:ℕ) ≤ d - 1 := by omega
    exact_mod_cast this
  have hKconn : IsConnected {ω : Eucl d | ω ∈ K ∧ ‖ω‖ = 1} := isConnected_sphere_submodule K hrankK
  have hIccconn : IsConnected (Set.Icc a b) := isConnected_Icc hab
  have hprodconn : IsConnected ({ω : Eucl d | ω ∈ K ∧ ‖ω‖ = 1} ×ˢ Set.Icc a b) :=
    hKconn.prod hIccconn
  set Ψ : Eucl d × ℝ → Eucl d := fun p => p.2 • (u:Eucl d) + Real.sqrt (1 - p.2^2) • p.1 with hΨdef
  have hΨcont : Continuous Ψ := by
    rw [hΨdef]
    fun_prop
  have hun : ‖(u:Eucl d)‖ = 1 := by
    have := u.2; rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at this; exact this
  have himg : Ψ '' ({ω : Eucl d | ω ∈ K ∧ ‖ω‖ = 1} ×ˢ Set.Icc a b)
      = {x : Eucl d | x ∈ sphere d ∧ a ≤ (⟪(u:Eucl d), x⟫:ℝ) ∧ (⟪(u:Eucl d), x⟫:ℝ) ≤ b} := by
    ext x
    simp only [Set.mem_image, Set.mem_prod, Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · rintro ⟨⟨ω, t⟩, ⟨⟨hωK, hωnorm⟩, ⟨hta, htb⟩⟩, hΨeq⟩
      rw [hΨdef] at hΨeq
      simp only at hΨeq
      have hωperp : (⟪(u:Eucl d), ω⟫ : ℝ) = 0 := by
        have := hωK
        rw [hKdef, LinearMap.mem_ker] at this
        simpa using this
      have hnorm1 : ‖t • (u:Eucl d) + Real.sqrt (1 - t^2) • ω‖ = 1 := by
        have hun' : ‖(u:Eucl d)‖ = 1 := hun
        have hs2 : (0:ℝ) ≤ 1 - t^2 := by nlinarith
        have hsq : Real.sqrt (1-t^2) ^ 2 = 1 - t^2 := Real.sq_sqrt hs2
        have hsqnn : 0 ≤ Real.sqrt (1-t^2) := Real.sqrt_nonneg _
        have hn2 : ‖t • (u:Eucl d) + Real.sqrt (1 - t^2) • ω‖^2 = 1 := by
          rw [norm_add_sq_real, norm_smul, norm_smul, hun', hωnorm, real_inner_smul_left,
            real_inner_smul_right, hωperp]
          simp only [Real.norm_eq_abs, mul_zero, add_zero, mul_one, sq_abs, abs_of_nonneg hsqnn]
          nlinarith [hsq]
        have hnn : (0:ℝ) ≤ ‖t • (u:Eucl d) + Real.sqrt (1 - t^2) • ω‖ := norm_nonneg _
        rw [show ‖t • (u:Eucl d) + Real.sqrt (1 - t^2) • ω‖
            = Real.sqrt (‖t • (u:Eucl d) + Real.sqrt (1 - t^2) • ω‖^2) from (Real.sqrt_sq hnn).symm,
          hn2, Real.sqrt_one]
      have hproj : (⟪(u:Eucl d), t • (u:Eucl d) + Real.sqrt (1 - t^2) • ω⟫ : ℝ) = t := by
        rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hωperp,
          real_inner_self_eq_norm_sq, hun]
        ring
      refine ⟨?_, ?_, ?_⟩
      · rw [MeasureToMeasure.sphere, Metric.mem_sphere, dist_eq_norm, sub_zero, ← hΨeq]
        exact hnorm1
      · rw [← hΨeq, hproj]; exact hta
      · rw [← hΨeq, hproj]; exact htb
    · rintro ⟨hxs, hta, htb⟩
      have hxnorm : ‖x‖ = 1 := by
        rw [MeasureToMeasure.sphere] at hxs
        exact norm_eq_one_of_mem_sphere hxs
      have hK1 : 1 ≤ Module.finrank ℝ K := by rw [hfinK]; omega
      obtain ⟨ω, hωK, hωnorm, hΨeq⟩ := exists_omega_apply u hK1 x hxnorm
      refine ⟨(ω, (⟪(u:Eucl d), x⟫ : ℝ)), ⟨⟨hωK, hωnorm⟩, ⟨hta, htb⟩⟩, ?_⟩
      rw [hΨdef]
      exact hΨeq
  rw [← himg]
  exact hprodconn.image Ψ hΨcont.continuousOn

end MeasureToMeasure.Leaves
