import MeasureToMeasure.Leaves.GeodesicArcChain
import MeasureToMeasure.Leaves.PoleGeometry
import Mathlib.GroupTheory.CosetCover

/-!
# Arc hop corridors between sphere points, clearing finitely many obstacles (lemma 5.4, G8)

The merge-tolerant relocation engine (`exists_merge_tolerant_relocation`) consumes its corridor
bundle as data: per relocated ball, a chain of on-sphere hop centres with per-hop capture and gate
radii whose gate balls clear every not-yet-moved source ball and every already-placed landing
ball. This file produces that data: for any two sphere points `x, y` (possibly equal, possibly
antipodal) and finitely many on-sphere obstacle points distinct from both, there is a hop chain
from `x` to `y` and a clearance `c > 0` whose gate balls stay `c`-clear of every obstacle.

**Construction (the waypoint two-arc detour).** A fresh waypoint `v` is chosen on the sphere off
the finitely many 2-planes `span {x, y}`, `span {x, qᵢ}`, `span {y, qᵢ}`: a finite union of
proper subspaces cannot cover `Eucl d` (Mathlib's `Subspace.exists_eq_top_of_iUnion_eq_univ`,
over an infinite field), the planes are proper because `3 ≤ d` supplies a unit vector orthogonal
to any two given vectors (`exists_unit_orthogonal_two`), and covering the sphere would cover the
whole space by scaling. The corridor is then the geodesic arc `x → v` followed by `v → y`. An
obstacle on an arc would lie in the arc's 2-plane, which the span-avoidance of `v` reduces to the
two antipode cases `q = -base` (excluded by the arc being strictly shorter than `π`) and
`q = -target` (excluded by the tangent sign: `⟪tangent, arc θ⟫ = sin θ ≥ 0` on `[0, Θ]` while
`⟪tangent, -target⟫ = -sin Θ < 0`). Compactness of the arcs then gives a uniform clearance
`c₀ > 0`, and subdividing both arcs into hops of length `≤ c₀/8` yields capture radii `3c₀/8`,
gate radii `c₀/2`, and obstacle clearance `c := c₀/16`, with every bound the relocation engine
needs (`dist + c ≤ a < b ≤ 2`, gates disjoint from the `c`-balls of every obstacle).
-/

set_option autoImplicit false

namespace MeasureToMeasure.Leaves

open Set MeasureTheory
open scoped RealInnerProductSpace

variable {d : ℕ}

/-- **A span of two vectors is never everything when `3 ≤ d`.** A unit vector orthogonal to both
generators (`exists_unit_orthogonal_two`) cannot be a linear combination of them. -/
theorem span_pair_ne_top (hd : 3 ≤ d) {x : Eucl d} (hx0 : x ≠ 0) (q : Eucl d) :
    Submodule.span ℝ {x, q} ≠ ⊤ := by
  intro htop
  obtain ⟨w, hwx, hwq, hwn⟩ := exists_unit_orthogonal_two hd hx0 q
  have hw : w ∈ Submodule.span ℝ {x, q} := htop ▸ Submodule.mem_top
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hw
  have hz : (⟪w, w⟫ : ℝ) = 0 := by
    calc (⟪w, w⟫ : ℝ) = ⟪a • x + b • q, w⟫ := by rw [hab]
      _ = a * (⟪x, w⟫ : ℝ) + b * (⟪q, w⟫ : ℝ) := by
          rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
      _ = 0 := by
          rw [hwx, hwq]
          ring
  rw [real_inner_self_eq_norm_sq, hwn] at hz
  norm_num at hz

/-- **A sphere point off finitely many proper subspaces.** A finite family of proper subspaces
cannot cover `Eucl d` (over the infinite field `ℝ`), and cannot cover the sphere either, since
covering the sphere covers every nonzero vector by scaling and `0` lies in any subspace. -/
theorem exists_sphere_point_off_submodules (hd1 : 1 ≤ d) {ι : Type*} [Finite ι]
    (V : ι → Submodule ℝ (Eucl d)) (hV : ∀ i, V i ≠ ⊤) :
    ∃ v : Eucl d, v ∈ sphere d ∧ ∀ i, v ∉ V i := by
  haveI : NeZero d := ⟨by omega⟩
  haveI : Nontrivial (Eucl d) := by
    refine ⟨EuclideanSpace.single (0 : Fin d) (1 : ℝ), 0, fun h => ?_⟩
    have h0 := congrFun (congrArg (fun z : Eucl d => (z : Fin d → ℝ)) h) 0
    simp at h0
  -- extend the family by `⊥` so the escape point is automatically nonzero
  set V' : Option ι → Submodule ℝ (Eucl d) := fun o => o.elim ⊥ V with hV'def
  have hV' : ∀ o, V' o ≠ ⊤ := by
    intro o
    match o with
    | none => exact bot_ne_top
    | some i => exact hV i
  have hcover : (⋃ o, (V' o : Set (Eucl d))) ≠ Set.univ := by
    intro hcov
    obtain ⟨o, ho⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hcov
    exact hV' o ho
  obtain ⟨u, hu⟩ := Set.ne_univ_iff_exists_notMem _ |>.mp hcover
  have hu' : ∀ o, u ∉ V' o := by
    intro o hmem
    exact hu (Set.mem_iUnion.mpr ⟨o, hmem⟩)
  have hu0 : u ≠ 0 := fun h => hu' none (h ▸ Submodule.zero_mem ⊥)
  refine ⟨‖u‖⁻¹ • u, normalize_mem_sphere hu0, fun i hmem => ?_⟩
  have : u ∈ V i := by
    have h2 : ‖u‖ • ‖u‖⁻¹ • u ∈ V i := Submodule.smul_mem _ _ hmem
    rwa [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hu0), one_smul] at h2
  exact hu' (some i) this

/-- The geodesic arc lives in the 2-plane of its endpoints. -/
theorem geodesicArc_mem_span (p q : Eucl d) (θ : ℝ) :
    geodesicArc p q θ ∈ Submodule.span ℝ {p, q} := by
  have hp : p ∈ Submodule.span ℝ {p, q} := Submodule.subset_span (by simp)
  have hq : q ∈ Submodule.span ℝ {p, q} := Submodule.subset_span (by simp)
  have ht : geodesicTangent p q ∈ Submodule.span ℝ {p, q} := by
    rw [geodesicTangent]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hq (Submodule.smul_mem _ _ hp))
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hp) (Submodule.smul_mem _ _ ht)

/-- **Pair-span flip.** A member of `span {c₁, c₂}` that is not colinear with `c₁` pins `c₂`
into the span of `c₁` and itself. -/
theorem mem_span_pair_flip {c₁ c₂ z : Eucl d} (hz : z ∈ Submodule.span ℝ {c₁, c₂})
    (hz1 : z ∉ Submodule.span ℝ ({c₁} : Set (Eucl d))) :
    c₂ ∈ Submodule.span ℝ {c₁, z} := by
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hz
  have hb : b ≠ 0 := by
    intro h0
    exact hz1 (Submodule.mem_span_singleton.mpr ⟨a, by rw [← hab, h0, zero_smul, add_zero]⟩)
  refine Submodule.mem_span_pair.mpr ⟨-(b⁻¹ * a), b⁻¹, ?_⟩
  have h1 : b⁻¹ • z = (b⁻¹ * a) • c₁ + c₂ := by
    rw [← hab, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hb, one_smul]
  rw [h1, neg_smul]
  abel

/-- **The closed short arc misses an obstacle** whose only chances of lying on the arc's 2-plane
are the two antipodes: `-base` is farther than the whole arc (`θ = π > Θ`), and `-target` has
negative tangent component while every arc point has `sin θ ≥ 0`. -/
theorem geodesicArc_avoids {p q obq : Eucl d} (hp : p ∈ sphere d) (hq : q ∈ sphere d)
    (_hobq : obq ∈ sphere d) (hnp : q ∉ Submodule.span ℝ ({p} : Set (Eucl d)))
    (hspan : obq ∈ Submodule.span ℝ {p, q} → obq = -p ∨ obq = -q)
    {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (geodesicDist p q)) : geodesicArc p q θ ≠ obq := by
  have hqp : q ≠ p := fun h =>
    hnp (by rw [h]; exact Submodule.mem_span_singleton_self p)
  have hqnp : q ≠ -p := fun h =>
    hnp (by rw [h]; exact Submodule.mem_span_singleton.mpr ⟨-1, by rw [neg_one_smul]⟩)
  have hinner : (⟪q, p⟫ : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := inner_mem_Ioo_of_ne hq hp hqp hqnp
  set Θ : ℝ := geodesicDist p q with hΘdef
  have hΘpi : Θ < Real.pi := by
    rw [hΘdef, geodesicDist, real_inner_comm]
    exact Real.arccos_lt_pi.mpr hinner.1
  have hΘpos : 0 < Θ := by
    rw [hΘdef, geodesicDist, real_inner_comm]
    exact Real.arccos_pos.mpr hinner.2
  intro heq
  rcases hspan (heq ▸ geodesicArc_mem_span p q θ) with hcase | hcase
  · -- `obq = -p`: the arc point at `θ ≤ Θ < π` cannot be the antipode of the base
    have hθpi : geodesicDist p (geodesicArc p q θ) = θ :=
      geodesicDist_geodesicArc hp q ⟨hθ.1, le_trans hθ.2 (le_of_lt hΘpi)⟩
    rw [heq, hcase] at hθpi
    have hpn : ‖p‖ = 1 := norm_eq_one_of_mem_sphere hp
    have hinnerpp : (⟪p, -p⟫ : ℝ) = -1 := by
      rw [inner_neg_right, real_inner_self_eq_norm_sq, hpn]
      norm_num
    rw [geodesicDist, hinnerpp, Real.arccos_neg_one] at hθpi
    have hθΘ : θ ≤ Θ := hθ.2
    linarith
  · -- `obq = -q`: negative tangent component, impossible for `sin θ ≥ 0`
    have htq : (⟪geodesicTangent p q, q⟫ : ℝ) = Real.sin Θ := by
      have harcΘ : geodesicArc p q Θ = q := geodesicArc_geodesicDist hp hq hqp hqnp
      have htn : ‖geodesicTangent p q‖ = 1 :=
        norm_eq_one_of_mem_sphere (geodesicTangent_mem_sphere hp hq hqp hqnp)
      have hort : (⟪p, geodesicTangent p q⟫ : ℝ) = 0 := inner_geodesicTangent_eq_zero hp q
      have hort2 : (⟪geodesicTangent p q, p⟫ : ℝ) = 0 := by
        rw [real_inner_comm]; exact hort
      calc (⟪geodesicTangent p q, q⟫ : ℝ) = ⟪geodesicTangent p q, geodesicArc p q Θ⟫ := by
            rw [harcΘ]
        _ = Real.sin Θ := by
            rw [geodesicArc, inner_add_right, real_inner_smul_right, real_inner_smul_right,
              hort2, real_inner_self_eq_norm_sq, htn]
            ring
    have htarc : (⟪geodesicTangent p q, geodesicArc p q θ⟫ : ℝ) = Real.sin θ := by
      have htn : ‖geodesicTangent p q‖ = 1 :=
        norm_eq_one_of_mem_sphere (geodesicTangent_mem_sphere hp hq hqp hqnp)
      have hort : (⟪p, geodesicTangent p q⟫ : ℝ) = 0 := inner_geodesicTangent_eq_zero hp q
      have hort2 : (⟪geodesicTangent p q, p⟫ : ℝ) = 0 := by
        rw [real_inner_comm]; exact hort
      rw [geodesicArc, inner_add_right, real_inner_smul_right, real_inner_smul_right,
        hort2, real_inner_self_eq_norm_sq, htn]
      ring
    have hsinΘ : 0 < Real.sin Θ := Real.sin_pos_of_pos_of_lt_pi hΘpos hΘpi
    have hsinθ : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2])
    rw [heq, hcase, inner_neg_right, htq] at htarc
    linarith

/-- Chord distance along an arc is at most twice the parameter gap (`cos`, `sin` are
1-Lipschitz). -/
theorem dist_geodesicArc_le {p q : Eucl d} (hp : p ∈ sphere d) (hq : q ∈ sphere d)
    (hqp : q ≠ p) (hqnp : q ≠ -p) (θ₁ θ₂ : ℝ) :
    dist (geodesicArc p q θ₁) (geodesicArc p q θ₂) ≤ 2 * |θ₁ - θ₂| := by
  have hpn : ‖p‖ = 1 := norm_eq_one_of_mem_sphere hp
  have htn : ‖geodesicTangent p q‖ = 1 :=
    norm_eq_one_of_mem_sphere (geodesicTangent_mem_sphere hp hq hqp hqnp)
  have hdiff : geodesicArc p q θ₁ - geodesicArc p q θ₂
      = (Real.cos θ₁ - Real.cos θ₂) • p + (Real.sin θ₁ - Real.sin θ₂) • geodesicTangent p q := by
    rw [geodesicArc, geodesicArc, sub_smul, sub_smul]
    abel
  have hcos : |Real.cos θ₁ - Real.cos θ₂| ≤ |θ₁ - θ₂| := by
    have h := Real.lipschitzWith_cos.dist_le_mul θ₁ θ₂
    rwa [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] at h
  have hsin : |Real.sin θ₁ - Real.sin θ₂| ≤ |θ₁ - θ₂| := by
    have h := Real.lipschitzWith_sin.dist_le_mul θ₁ θ₂
    rwa [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] at h
  calc dist (geodesicArc p q θ₁) (geodesicArc p q θ₂)
      = ‖(Real.cos θ₁ - Real.cos θ₂) • p
          + (Real.sin θ₁ - Real.sin θ₂) • geodesicTangent p q‖ := by
        rw [dist_eq_norm, hdiff]
    _ ≤ ‖(Real.cos θ₁ - Real.cos θ₂) • p‖
          + ‖(Real.sin θ₁ - Real.sin θ₂) • geodesicTangent p q‖ := norm_add_le _ _
    _ = |Real.cos θ₁ - Real.cos θ₂| + |Real.sin θ₁ - Real.sin θ₂| := by
        rw [norm_smul, norm_smul, hpn, htn, mul_one, mul_one, Real.norm_eq_abs,
          Real.norm_eq_abs]
    _ ≤ 2 * |θ₁ - θ₂| := by linarith

/-- **Uniform clearance of a closed arc from finitely many avoided points.** -/
theorem exists_arc_clearance {p q : Eucl d} (hcont : Continuous (geodesicArc p q))
    {Θ : ℝ} (hΘ : 0 ≤ Θ) {P : ℕ} (obs : Fin P → Eucl d)
    (havoid : ∀ i, ∀ θ ∈ Set.Icc 0 Θ, geodesicArc p q θ ≠ obs i) :
    ∃ c : ℝ, 0 < c ∧ ∀ θ ∈ Set.Icc 0 Θ, ∀ i, c ≤ dist (geodesicArc p q θ) (obs i) := by
  classical
  set A : Set (Eucl d) := geodesicArc p q '' Set.Icc 0 Θ with hAdef
  have hAcomp : IsCompact A := (isCompact_Icc).image hcont
  have hAne : A.Nonempty := ⟨geodesicArc p q 0, 0, ⟨le_rfl, hΘ⟩, rfl⟩
  have hpos : ∀ i, 0 < Metric.infDist (obs i) A := by
    intro i
    refine (hAcomp.isClosed.notMem_iff_infDist_pos hAne).mp ?_
    rintro ⟨θ, hθmem, hθeq⟩
    exact havoid i θ hθmem hθeq
  rcases Nat.eq_zero_or_pos P with hP | hP
  · subst hP
    exact ⟨1, one_pos, fun θ _ i => i.elim0⟩
  · haveI : Nonempty (Fin P) := ⟨⟨0, hP⟩⟩
    have hne : (Finset.univ : Finset (Fin P)).Nonempty := Finset.univ_nonempty
    refine ⟨Finset.univ.inf' hne (fun i => Metric.infDist (obs i) A),
      (Finset.lt_inf'_iff hne).mpr fun i _ => hpos i, ?_⟩
    intro θ hθ i
    calc Finset.univ.inf' hne (fun i => Metric.infDist (obs i) A)
        ≤ Metric.infDist (obs i) A := Finset.inf'_le _ (Finset.mem_univ i)
      _ ≤ dist (obs i) (geodesicArc p q θ) :=
          Metric.infDist_le_dist_of_mem ⟨θ, hθ, rfl⟩
      _ = dist (geodesicArc p q θ) (obs i) := dist_comm _ _

/-- A unit vector colinear with a unit vector is it or its antipode. -/
theorem eq_or_eq_neg_of_mem_span_singleton_unit {u z : Eucl d} (hu : ‖u‖ = 1) (hz : ‖z‖ = 1)
    (h : z ∈ Submodule.span ℝ ({u} : Set (Eucl d))) : z = u ∨ z = -u := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
  have hnorm : ‖z‖ = |c| * ‖u‖ := by rw [← hc, norm_smul, Real.norm_eq_abs]
  rw [hz, hu, mul_one] at hnorm
  rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hnorm.symm with h1 | h1
  · left; rw [← hc, h1, one_smul]
  · right; rw [← hc, h1, neg_one_smul]

/-- **Arc hop corridor between two sphere points, clearing finitely many obstacle points.**
For `x, y` on the sphere (`3 ≤ d`; `x = y` and `y = -x` both allowed) and finitely many
on-sphere obstacles distinct from `x` and `y`, there are a clearance `c > 0` and a hop chain
`w 0 = x, …, w M = y` of on-sphere centres with capture and gate radii satisfying every bound
the merge-tolerant relocation engine's corridor bundle demands: `dist + c ≤ a t < b t ≤ 2`, and
every gate ball disjoint from the closed `c`-ball of every obstacle. Consumers instantiate the
engine's staging radius `ρ` and the obstacle-ball radii at any values `≤ c`. Waypoint two-arc
construction; see the module docstring. -/
theorem exists_arc_hop_corridor (hd : 3 ≤ d) {x y : Eucl d}
    (hx : x ∈ sphere d) (hy : y ∈ sphere d)
    {P : ℕ} (q : Fin P → Eucl d) (hqs : ∀ i, q i ∈ sphere d)
    (hqx : ∀ i, q i ≠ x) (hqy : ∀ i, q i ≠ y) :
    ∃ c : ℝ, 0 < c ∧ ∃ (M : ℕ) (w : Fin (M + 1) → Eucl d) (a b : Fin M → ℝ),
      w 0 = x ∧ w (Fin.last M) = y ∧ (∀ t, w t ∈ sphere d) ∧
      (∀ t : Fin M, dist (w t.succ) (w t.castSucc) + c ≤ a t) ∧
      (∀ t, a t < b t) ∧ (∀ t, b t ≤ 2) ∧
      (∀ (t : Fin M) (i : Fin P),
        Disjoint (Metric.ball (w t.succ) (b t)) (Metric.closedBall (q i) c)) := by
  classical
  have hxn : ‖x‖ = 1 := norm_eq_one_of_mem_sphere hx
  have hyn : ‖y‖ = 1 := norm_eq_one_of_mem_sphere hy
  have hx0 : x ≠ 0 := fun h => by rw [h, norm_zero] at hxn; exact zero_ne_one hxn
  have hy0 : y ≠ 0 := fun h => by rw [h, norm_zero] at hyn; exact zero_ne_one hyn
  -- the waypoint, off every relevant 2-plane
  set V : Option (Fin P ⊕ Fin P) → Submodule ℝ (Eucl d) := fun o =>
    match o with
    | none => Submodule.span ℝ {x, y}
    | some (Sum.inl i) => Submodule.span ℝ {x, q i}
    | some (Sum.inr i) => Submodule.span ℝ {y, q i} with hVdef
  have hV : ∀ o, V o ≠ ⊤ := by
    intro o
    match o with
    | none => exact span_pair_ne_top hd hx0 y
    | some (Sum.inl i) => exact span_pair_ne_top hd hx0 (q i)
    | some (Sum.inr i) => exact span_pair_ne_top hd hy0 (q i)
  obtain ⟨v, hv, hvoff⟩ := exists_sphere_point_off_submodules (by omega) V hV
  have hvn : ‖v‖ = 1 := norm_eq_one_of_mem_sphere hv
  have hvxy : v ∉ Submodule.span ℝ {x, y} := hvoff none
  have hvxq : ∀ i, v ∉ Submodule.span ℝ {x, q i} := fun i => hvoff (some (Sum.inl i))
  have hvyq : ∀ i, v ∉ Submodule.span ℝ {y, q i} := fun i => hvoff (some (Sum.inr i))
  have hvx : v ∉ Submodule.span ℝ ({x} : Set (Eucl d)) := fun h =>
    hvxy (Submodule.span_mono (Set.singleton_subset_iff.mpr (by simp)) h)
  have hvy : v ∉ Submodule.span ℝ ({y} : Set (Eucl d)) := fun h =>
    hvxy (Submodule.span_mono (Set.singleton_subset_iff.mpr (by simp)) h)
  -- nondegeneracy of both arcs
  have hvnex : v ≠ x := fun h =>
    hvx (by rw [h]; exact Submodule.mem_span_singleton_self x)
  have hvnenx : v ≠ -x := fun h =>
    hvx (by rw [h]; exact Submodule.mem_span_singleton.mpr ⟨-1, by rw [neg_one_smul]⟩)
  have hyv : y ∉ Submodule.span ℝ ({v} : Set (Eucl d)) := by
    intro hmem
    obtain ⟨cy, hcy⟩ := Submodule.mem_span_singleton.mp hmem
    have hcy0 : cy ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hcy
      exact hy0 hcy.symm
    refine hvy (Submodule.mem_span_singleton.mpr ⟨cy⁻¹, ?_⟩)
    rw [← hcy, smul_smul, inv_mul_cancel₀ hcy0, one_smul]
  have hynev : y ≠ v := fun h =>
    hyv (by rw [h]; exact Submodule.mem_span_singleton_self v)
  have hynenv : y ≠ -v := fun h =>
    hyv (by rw [h]; exact Submodule.mem_span_singleton.mpr ⟨-1, by rw [neg_one_smul]⟩)
  -- both legs avoid every obstacle
  set Θ₁ : ℝ := geodesicDist x v with hΘ₁def
  set Θ₂ : ℝ := geodesicDist v y with hΘ₂def
  have havoid₁ : ∀ i, ∀ θ ∈ Set.Icc 0 Θ₁, geodesicArc x v θ ≠ q i := by
    intro i θ hθ
    refine geodesicArc_avoids hx hv (hqs i) hvx ?_ hθ
    intro hmem
    by_cases hqspanx : q i ∈ Submodule.span ℝ ({x} : Set (Eucl d))
    · rcases eq_or_eq_neg_of_mem_span_singleton_unit hxn
        (norm_eq_one_of_mem_sphere (hqs i)) hqspanx with h1 | h1
      · exact absurd h1 (hqx i)
      · exact Or.inl h1
    · exact absurd (mem_span_pair_flip hmem hqspanx) (hvxq i)
  have havoid₂ : ∀ i, ∀ θ ∈ Set.Icc 0 Θ₂, geodesicArc v y θ ≠ q i := by
    intro i θ hθ
    refine geodesicArc_avoids hv hy (hqs i) hyv ?_ hθ
    intro hmem
    by_cases hqspany : q i ∈ Submodule.span ℝ ({y} : Set (Eucl d))
    · rcases eq_or_eq_neg_of_mem_span_singleton_unit hyn
        (norm_eq_one_of_mem_sphere (hqs i)) hqspany with h1 | h1
      · exact absurd h1 (hqy i)
      · exact Or.inr h1
    · rw [Set.pair_comm v y] at hmem
      exact absurd (mem_span_pair_flip hmem hqspany) (hvyq i)
  -- uniform clearance of both arcs, capped at 1
  have hΘ₁mem : Θ₁ ∈ Set.Icc 0 Real.pi := geodesicDist_mem_Icc x v
  have hΘ₂mem : Θ₂ ∈ Set.Icc 0 Real.pi := geodesicDist_mem_Icc v y
  obtain ⟨c₁, hc₁pos, hc₁⟩ :=
    exists_arc_clearance (continuous_geodesicArc x v) hΘ₁mem.1 q havoid₁
  obtain ⟨c₂, hc₂pos, hc₂⟩ :=
    exists_arc_clearance (continuous_geodesicArc v y) hΘ₂mem.1 q havoid₂
  set c₀ : ℝ := min (min c₁ c₂) 1 with hc₀def
  have hc₀pos : 0 < c₀ := lt_min (lt_min hc₁pos hc₂pos) one_pos
  have hc₀le1 : c₀ ≤ 1 := min_le_right _ _
  have hc₀c₁ : c₀ ≤ c₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hc₀c₂ : c₀ ≤ c₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  -- positive arc lengths and subdivisions
  have hinner₁ : (⟪v, x⟫ : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := inner_mem_Ioo_of_ne hv hx hvnex hvnenx
  have hΘ₁pos : 0 < Θ₁ := by
    rw [hΘ₁def, geodesicDist, real_inner_comm]
    exact Real.arccos_pos.mpr hinner₁.2
  have hinner₂ : (⟪y, v⟫ : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := inner_mem_Ioo_of_ne hy hv hynev hynenv
  have hΘ₂pos : 0 < Θ₂ := by
    rw [hΘ₂def, geodesicDist, real_inner_comm]
    exact Real.arccos_pos.mpr hinner₂.2
  set h : ℝ := c₀ / 8 with hhdef
  have hhpos : 0 < h := by positivity
  set M₁ : ℕ := ⌈Θ₁ / h⌉₊ with hM₁def
  set M₂ : ℕ := ⌈Θ₂ / h⌉₊ with hM₂def
  have hM₁pos : 0 < M₁ := Nat.ceil_pos.mpr (div_pos hΘ₁pos hhpos)
  have hM₂pos : 0 < M₂ := Nat.ceil_pos.mpr (div_pos hΘ₂pos hhpos)
  set s₁ : ℝ := Θ₁ / M₁ with hs₁def
  set s₂ : ℝ := Θ₂ / M₂ with hs₂def
  have hM₁R : (0 : ℝ) < (M₁ : ℝ) := by exact_mod_cast hM₁pos
  have hM₂R : (0 : ℝ) < (M₂ : ℝ) := by exact_mod_cast hM₂pos
  have hs₁pos : 0 < s₁ := div_pos hΘ₁pos hM₁R
  have hs₂pos : 0 < s₂ := div_pos hΘ₂pos hM₂R
  have hs₁h : s₁ ≤ h := by
    rw [hs₁def, div_le_iff₀ hM₁R]
    have := Nat.le_ceil (Θ₁ / h)
    rw [← hM₁def] at this
    calc Θ₁ = (Θ₁ / h) * h := by field_simp
      _ ≤ (M₁ : ℝ) * h := by
          exact mul_le_mul_of_nonneg_right this hhpos.le
      _ = h * (M₁ : ℝ) := by ring
  have hs₂h : s₂ ≤ h := by
    rw [hs₂def, div_le_iff₀ hM₂R]
    have := Nat.le_ceil (Θ₂ / h)
    rw [← hM₂def] at this
    calc Θ₂ = (Θ₂ / h) * h := by field_simp
      _ ≤ (M₂ : ℝ) * h := by
          exact mul_le_mul_of_nonneg_right this hhpos.le
      _ = h * (M₂ : ℝ) := by ring
  have hM₁s₁ : (M₁ : ℝ) * s₁ = Θ₁ := by rw [hs₁def]; field_simp
  have hM₂s₂ : (M₂ : ℝ) * s₂ = Θ₂ := by rw [hs₂def]; field_simp
  have harc₁v : geodesicArc x v Θ₁ = v := geodesicArc_geodesicDist hx hv hvnex hvnenx
  have harc₂y : geodesicArc v y Θ₂ = y := geodesicArc_geodesicDist hv hy hynev hynenv
  -- the concatenated chain
  set M : ℕ := M₁ + M₂ with hMdef
  set w : Fin (M + 1) → Eucl d := fun t =>
    if (t : ℕ) ≤ M₁ then geodesicArc x v ((t : ℕ) * s₁)
    else geodesicArc v y (((t : ℕ) - M₁ : ℕ) * s₂) with hwdef
  -- every chain point sits on one of the two arcs, with parameter in range
  have hwmem : ∀ t : Fin (M + 1), w t ∈ sphere d := by
    intro t
    simp only [hwdef]
    by_cases hcase : (t : ℕ) ≤ M₁
    · rw [if_pos hcase]
      exact geodesicArc_mem_sphere hx hv hvnex hvnenx _
    · rw [if_neg hcase]
      exact geodesicArc_mem_sphere hv hy hynev hynenv _
  have hwclear : ∀ t : Fin (M + 1), ∀ i, c₀ ≤ dist (w t) (q i) := by
    intro t i
    simp only [hwdef]
    by_cases hcase : (t : ℕ) ≤ M₁
    · rw [if_pos hcase]
      refine le_trans hc₀c₁ (hc₁ _ ⟨by positivity, ?_⟩ i)
      calc ((t : ℕ) : ℝ) * s₁ ≤ (M₁ : ℝ) * s₁ := by
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcase) hs₁pos.le
        _ = Θ₁ := hM₁s₁
    · rw [if_neg hcase]
      refine le_trans hc₀c₂ (hc₂ _ ⟨by positivity, ?_⟩ i)
      have htM : (t : ℕ) - M₁ ≤ M₂ := by omega
      calc (((t : ℕ) - M₁ : ℕ) : ℝ) * s₂ ≤ (M₂ : ℝ) * s₂ := by
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast htM) hs₂pos.le
        _ = Θ₂ := hM₂s₂
  -- per-hop displacement bound
  have hhop : ∀ t : Fin M, dist (w t.succ) (w t.castSucc) ≤ c₀ / 4 := by
    intro t
    have hsuccval : (t.succ : ℕ) = (t : ℕ) + 1 := rfl
    have hcastval : (t.castSucc : ℕ) = (t : ℕ) := rfl
    simp only [hwdef]
    by_cases hcase : (t : ℕ) + 1 ≤ M₁
    · -- both on the first arc
      rw [hsuccval, hcastval, if_pos hcase, if_pos (by omega)]
      calc dist (geodesicArc x v (((t : ℕ) + 1 : ℕ) * s₁))
            (geodesicArc x v ((t : ℕ) * s₁))
          ≤ 2 * |(((t : ℕ) + 1 : ℕ) : ℝ) * s₁ - ((t : ℕ) : ℝ) * s₁| :=
            dist_geodesicArc_le hx hv hvnex hvnenx _ _
        _ = 2 * s₁ := by
            rw [show (((t : ℕ) + 1 : ℕ) : ℝ) * s₁ - ((t : ℕ) : ℝ) * s₁ = s₁ by push_cast; ring,
              abs_of_pos hs₁pos]
        _ ≤ c₀ / 4 := by rw [hhdef] at hs₁h; linarith
    · by_cases hcase2 : (t : ℕ) ≤ M₁
      · -- the junction hop: from `v` into the second arc
        have htM₁ : (t : ℕ) = M₁ := by omega
        rw [hsuccval, hcastval, if_neg (by omega), if_pos hcase2, htM₁]
        have h1 : ((M₁ : ℕ) : ℝ) * s₁ = Θ₁ := hM₁s₁
        have h2 : (M₁ + 1 - M₁ : ℕ) = 1 := by omega
        rw [h1, harc₁v, h2]
        calc dist (geodesicArc v y ((1 : ℕ) * s₂)) v
            = dist (geodesicArc v y ((1 : ℕ) * s₂)) (geodesicArc v y 0) := by
              rw [geodesicArc_zero]
          _ ≤ 2 * |((1 : ℕ) : ℝ) * s₂ - 0| := dist_geodesicArc_le hv hy hynev hynenv _ _
          _ = 2 * s₂ := by
              rw [show ((1 : ℕ) : ℝ) * s₂ - 0 = s₂ by push_cast; ring, abs_of_pos hs₂pos]
          _ ≤ c₀ / 4 := by rw [hhdef] at hs₂h; linarith
      · -- both on the second arc
        have htM₁ : M₁ < (t : ℕ) := by omega
        rw [hsuccval, hcastval, if_neg (by omega), if_neg (by omega)]
        have hsub : ((t : ℕ) + 1 - M₁ : ℕ) = ((t : ℕ) - M₁ : ℕ) + 1 := by omega
        rw [hsub]
        calc dist (geodesicArc v y ((((t : ℕ) - M₁ : ℕ) + 1 : ℕ) * s₂))
              (geodesicArc v y (((t : ℕ) - M₁ : ℕ) * s₂))
            ≤ 2 * |((((t : ℕ) - M₁ : ℕ) + 1 : ℕ) : ℝ) * s₂ - (((t : ℕ) - M₁ : ℕ) : ℝ) * s₂| :=
              dist_geodesicArc_le hv hy hynev hynenv _ _
          _ = 2 * s₂ := by
              rw [show ((((t : ℕ) - M₁ : ℕ) + 1 : ℕ) : ℝ) * s₂
                    - (((t : ℕ) - M₁ : ℕ) : ℝ) * s₂ = s₂ by push_cast; ring,
                abs_of_pos hs₂pos]
          _ ≤ c₀ / 4 := by rw [hhdef] at hs₂h; linarith
  -- assemble
  refine ⟨c₀ / 16, by positivity, M, w, fun _ => 3 * c₀ / 8, fun _ => c₀ / 2, ?_, ?_,
    hwmem, ?_, ?_, ?_, ?_⟩
  · -- start
    simp only [hwdef]
    have h0 : ((0 : Fin (M + 1)) : ℕ) = 0 := rfl
    rw [h0, if_pos (by omega)]
    rw [show ((0 : ℕ) : ℝ) * s₁ = 0 by push_cast; ring, geodesicArc_zero]
  · -- end
    simp only [hwdef]
    have hlast : ((Fin.last M : Fin (M + 1)) : ℕ) = M := rfl
    rw [hlast, if_neg (by omega)]
    have hsub : (M - M₁ : ℕ) = M₂ := by omega
    rw [hsub, show ((M₂ : ℕ) : ℝ) * s₂ = Θ₂ from hM₂s₂, harc₂y]
  · -- capture
    intro t
    have := hhop t
    linarith
  · -- capture < gate
    intro t
    linarith
  · -- gate ≤ 2
    intro t
    linarith
  · -- gates clear the obstacle balls
    intro t i
    rw [Set.disjoint_left]
    intro z hz hz'
    rw [Metric.mem_ball] at hz
    rw [Metric.mem_closedBall] at hz'
    have hclear := hwclear t.succ i
    have htri := dist_triangle (w t.succ) z (q i)
    rw [dist_comm (w t.succ) z] at htri
    linarith

end MeasureToMeasure.Leaves
