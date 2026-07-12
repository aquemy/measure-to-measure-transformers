import MeasureToMeasure.Leaves.VoronoiCell
import MeasureToMeasure.Leaves.AtomlessDirection
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.Clopen

/-!
# The Voronoi touching graph is connected (`prop_2_2` Stage 3, item 3 relay leaf 1)

For `M` distinct targets `x : Fin M → Eucl d`, the OPEN Voronoi cells `voronoiCell x k`
(`VoronoiCell.lean`) do not literally partition the sphere -- boundary ("tie") points belong to no
cell. This leaf shows their union is nonetheless DENSE, hence the cells' closures cover the sphere,
and uses that to show the "touching" relation (closures intersect) makes every pair of targets
mutually reachable through a finite chain of pairwise-touching cells -- the graph-connectivity fact
`gated_forest_to_target_retention`'s inter-cell routing (Stage 3 item 3) needs to turn an arbitrary
donor/recipient pair into a sequence of SHORT, pairwise-adjacent hops (leaf 3/4), rather than one
long-range connection that could cross through unrelated cells' territory.

**Why density, not a direct combinatorial argument.** A point where two or more targets tie for the
maximum inner product belongs to no open cell. The "tie zone" `Z` is a FINITE union (over pairs
`i ≠ j`) of hyperplane traces `{y ∈ sphere d | ⟪x i - x j, y⟫ = 0}` -- each already known
`toSphere`-null via `toSphere_ker_null` (`AtomlessDirection.lean`, built for an unrelated genericity
argument but exactly the fact needed here too). A finite union of null sets is null, and `toSphere`
is an `IsOpenPosMeasure`, so a null set has empty interior (`Measure.interior_eq_empty_of_null`) --
i.e. `Z`'s complement, the union of open cells, is dense. This sidesteps any case analysis on how
many targets tie at a given boundary point or whether the tie is "transversal": the argument never
inspects the LOCAL structure of `Z` at all, only its global measure.

**Connectivity itself** is then a direct closed-separation argument: if the touching graph split into
two groups with no cross-touching, the closures of their cell-unions would be disjoint closed sets
covering the (connected, `2 ≤ d`) sphere -- impossible.

M3b/mid-level staging: Stage 3 item 3 (Voronoi-adjacency relay) of the `prop_2_2` Steps 2-3
campaign; see project notes. Build order: this leaf (touching-graph connected) -> path extraction ->
per-hop straddle-ball chains -> multi-leg concatenation -> Stage 4 combine.
-/

namespace MeasureToMeasure.Leaves

open Set MeasureTheory
open scoped RealInnerProductSpace

variable {d : ℕ}

/-- **The tie zone is measure-zero.** For distinct targets, every sphere point that lies in no
open Voronoi cell has some pair of targets exactly tied for the maximum inner product (the
maximizer that beats it must be tied, not strictly worse, since it is itself a maximizer); the set
of such tied pairs' witnesses is covered by finitely many null hyperplane traces. -/
theorem toSphere_tieZone_null {M : ℕ} (hM : 0 < M) (x : Fin M → Eucl d)
    (hxinj : Function.Injective x) :
    (volume : Measure (Eucl d)).toSphere
      {u : Metric.sphere (0 : Eucl d) 1 | (u : Eucl d) ∉ ⋃ k, voronoiCell x k} = 0 := by
  apply measure_mono_null (t := ⋃ p : {p : Fin M × Fin M // p.1 ≠ p.2},
    {u : Metric.sphere (0 : Eucl d) 1 | (⟪(u : Eucl d), x p.1.1 - x p.1.2⟫ : ℝ) = 0})
  · intro u hu
    simp only [Set.mem_iUnion, not_exists] at hu
    have hus : (u : Eucl d) ∈ sphere d := u.2
    obtain ⟨k₀, -, hk₀max⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin M))
      (fun k => (⟪x k, (u : Eucl d)⟫ : ℝ)) ⟨⟨0, hM⟩, Finset.mem_univ _⟩
    have hnotcell : (u : Eucl d) ∉ voronoiCell x k₀ := hu k₀
    simp only [voronoiCell, Set.mem_setOf_eq, not_and, not_forall] at hnotcell
    obtain ⟨k₁, hk₁ne, hk₁ge⟩ := hnotcell hus
    push Not at hk₁ge
    have hk₁le : (⟪x k₁, (u : Eucl d)⟫ : ℝ) ≤ ⟪x k₀, (u : Eucl d)⟫ :=
      hk₀max k₁ (Finset.mem_univ k₁)
    have heq : (⟪x k₀, (u : Eucl d)⟫ : ℝ) = ⟪x k₁, (u : Eucl d)⟫ := le_antisymm hk₁ge hk₁le
    refine Set.mem_iUnion.mpr ⟨⟨(k₀, k₁), hk₁ne.symm⟩, ?_⟩
    show (⟪(u : Eucl d), x k₀ - x k₁⟫ : ℝ) = 0
    rw [inner_sub_right]
    linarith [heq, real_inner_comm (x k₀) (u : Eucl d), real_inner_comm (x k₁) (u : Eucl d)]
  · apply measure_iUnion_null
    intro p
    exact toSphere_ker_null (x p.1.1 - x p.1.2) (sub_ne_zero.mpr (hxinj.ne p.2))

/-- **The open Voronoi cells' union is dense, so their closures cover the sphere.** The
"IsOpenPosMeasure" instance for `toSphere` turns the tie zone's null measure into empty interior
(`Measure.interior_eq_empty_of_null`), i.e. density of the complement; density in the subtype
`sphere d` translates to the ambient sphere sitting inside the closure of the (finite) union of
open cells, and closure commutes with finite unions. -/
theorem sphere_subset_iUnion_closure_voronoiCell {M : ℕ} (hM : 0 < M) (x : Fin M → Eucl d)
    (hxinj : Function.Injective x) :
    sphere d ⊆ ⋃ k, closure (voronoiCell x k) := by
  set t : Set (Metric.sphere (0 : Eucl d) 1) :=
    {u : Metric.sphere (0 : Eucl d) 1 | (u : Eucl d) ∈ ⋃ k, voronoiCell x k} with htdef
  have htc : tᶜ = {u : Metric.sphere (0 : Eucl d) 1 | (u : Eucl d) ∉ ⋃ k, voronoiCell x k} := by
    ext u; simp [htdef]
  have hdense : Dense t := by
    rw [← compl_compl t]
    apply interior_eq_empty_iff_dense_compl.mp
    rw [htc]
    exact MeasureTheory.Measure.interior_eq_empty_of_null (toSphere_tieZone_null hM x hxinj)
  have himg : Subtype.val '' t = ⋃ k, voronoiCell x k := by
    ext y
    simp only [htdef, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro hy
      have hys : y ∈ sphere d := by
        obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hy
        exact voronoiCell_subset_sphere x k hk
      exact ⟨⟨y, hys⟩, hy, rfl⟩
  have hcov : sphere d ⊆ closure (Subtype.val '' t) := Subtype.dense_iff.mp hdense
  rw [himg, closure_iUnion_of_finite] at hcov
  exact hcov

/-- **A target lies in its own open cell**, given targets are on the sphere and pairwise
distinct: it beats every other target's inner product against itself outright, via the
equality case of Cauchy-Schwarz for unit vectors. -/
theorem mem_voronoiCell_self {M : ℕ} (x : Fin M → Eucl d) (hx : ∀ k, x k ∈ sphere d)
    (hxinj : Function.Injective x) (k : Fin M) : x k ∈ voronoiCell x k := by
  refine ⟨hx k, fun k' hk'ne => ?_⟩
  have h1 : ‖x k'‖ = 1 := norm_eq_one_of_mem_sphere (hx k')
  have h2 : ‖x k‖ = 1 := norm_eq_one_of_mem_sphere (hx k)
  have hlt := (inner_lt_one_iff_real_of_norm_eq_one h1 h2).mpr (hxinj.ne hk'ne)
  rwa [real_inner_self_eq_norm_sq, h2, one_pow]

/-- **A target is not in the closure of any other target's cell.** `voronoiCell x k` has empty
ambient interior (it sits inside the sphere), so this can't go through an "own cell is an open
neighborhood" argument -- instead, `x k` and `voronoiCell x k'` are strictly separated by the
AMBIENT open half-space `⟪x k' - x k, ·⟫ < 0`: every point of `voronoiCell x k'` beats `x k`
against `x k'` (so lands in the closed complementary half-space), while `x k` itself lands
strictly on the near side (strict Cauchy-Schwarz for distinct unit vectors). -/
theorem notMem_closure_voronoiCell_of_ne {M : ℕ} (x : Fin M → Eucl d) (hx : ∀ k, x k ∈ sphere d)
    (hxinj : Function.Injective x) {k k' : Fin M} (hne : k ≠ k') :
    x k ∉ closure (voronoiCell x k') := by
  have hxkc : (⟪x k' - x k, x k⟫ : ℝ) < 0 := by
    have h1 : ‖x k'‖ = 1 := norm_eq_one_of_mem_sphere (hx k')
    have h2 : ‖x k‖ = 1 := norm_eq_one_of_mem_sphere (hx k)
    have hlt := (inner_lt_one_iff_real_of_norm_eq_one h1 h2).mpr (hxinj.ne hne.symm)
    rw [inner_sub_left, real_inner_self_eq_norm_sq, h2]
    nlinarith
  have hsub : voronoiCell x k' ⊆ {y : Eucl d | (0 : ℝ) ≤ ⟪x k' - x k, y⟫} := by
    rintro y ⟨-, hy⟩
    have hlt := hy k hne
    show (0 : ℝ) ≤ ⟪x k' - x k, y⟫
    rw [inner_sub_left]
    linarith
  have hUc_closed : IsClosed {y : Eucl d | (0 : ℝ) ≤ ⟪x k' - x k, y⟫} :=
    isClosed_le continuous_const (by fun_prop)
  intro hmem
  exact absurd (closure_minimal hsub hUc_closed hmem) (not_le.mpr hxkc)

/-- Two targets' cells "touch": their closures share a point. -/
def voronoiAdjacent {M : ℕ} (x : Fin M → Eucl d) (j k : Fin M) : Prop :=
  (closure (voronoiCell x j) ∩ closure (voronoiCell x k)).Nonempty

theorem voronoiAdjacent_symm {M : ℕ} {x : Fin M → Eucl d} {j k : Fin M}
    (h : voronoiAdjacent x j k) : voronoiAdjacent x k j := by
  obtain ⟨y, hy1, hy2⟩ := h
  exact ⟨y, hy2, hy1⟩

/-- **The unit sphere of the full space is connected**, for `2 ≤ d`. -/
theorem isConnected_sphere_full (hd : 2 ≤ d) : IsConnected (sphere d) := by
  have hrank : 1 < Module.rank ℝ (Eucl d) := by
    rw [← Module.finrank_eq_rank']
    have h1 : 1 < Module.finrank ℝ (Eucl d) := by rw [finrank_euclideanSpace_fin]; omega
    exact_mod_cast h1
  exact isConnected_sphere hrank 0 (by norm_num)

/-- **The Voronoi touching graph is connected.** For `M` distinct sphere-supported targets and
`2 ≤ d`, any two targets are joined by a finite chain of pairwise-touching cells. If the
reachable set from `j` excluded some `k`, the reachable cells' closures and the unreachable
cells' closures would be disjoint closed sets covering the (connected) sphere -- impossible,
since each target sits in its own cell, so `x k` can only ever land in the "unreachable" piece
and `x j` only in the "reachable" piece, ruling out either piece alone covering everything. -/
theorem reflTransGen_voronoiAdjacent {M : ℕ} (hd : 2 ≤ d) (hM : 0 < M) (x : Fin M → Eucl d)
    (hx : ∀ k, x k ∈ sphere d) (hxinj : Function.Injective x) (j k : Fin M) :
    Relation.ReflTransGen (voronoiAdjacent x) j k := by
  by_contra hcon
  set G1 : Set (Fin M) := {k' | Relation.ReflTransGen (voronoiAdjacent x) j k'} with hG1def
  have hjG1 : j ∈ G1 := Relation.ReflTransGen.refl
  have hkG1c : k ∈ G1ᶜ := hcon
  set U1 : Set (Eucl d) := ⋃ k' ∈ G1, closure (voronoiCell x k') with hU1def
  set U2 : Set (Eucl d) := ⋃ k' ∈ G1ᶜ, closure (voronoiCell x k') with hU2def
  have hU1closed : IsClosed U1 := (Set.toFinite G1).isClosed_biUnion (fun k' _ => isClosed_closure)
  have hU2closed : IsClosed U2 :=
    (Set.toFinite G1ᶜ).isClosed_biUnion (fun k' _ => isClosed_closure)
  have hkey : ∀ (S : Set (Fin M)) (a : Fin M),
      x a ∈ ⋃ k' ∈ S, closure (voronoiCell x k') → a ∈ S := by
    intro S a ha
    obtain ⟨k', hk'S, hk'mem⟩ := Set.mem_iUnion₂.mp ha
    rcases eq_or_ne a k' with heq | hne
    · rwa [heq]
    · exact absurd hk'mem (notMem_closure_voronoiCell_of_ne x hx hxinj hne)
  have hcov : sphere d ⊆ U1 ∪ U2 := by
    intro y hy
    obtain ⟨k', hk'⟩ := Set.mem_iUnion.mp (sphere_subset_iUnion_closure_voronoiCell hM x hxinj hy)
    by_cases hk'G1 : k' ∈ G1
    · exact Or.inl (Set.mem_biUnion hk'G1 hk')
    · exact Or.inr (Set.mem_biUnion hk'G1 hk')
  have hdisj : Disjoint U1 U2 := by
    rw [Set.disjoint_left]
    rintro y hyU1 hyU2
    obtain ⟨k1, hk1G1, hk1⟩ := Set.mem_iUnion₂.mp hyU1
    obtain ⟨k2, hk2G1c, hk2⟩ := Set.mem_iUnion₂.mp hyU2
    exact hk2G1c (hk1G1.tail ⟨y, hk1, hk2⟩)
  have hsep := (isPreconnected_iff_subset_of_fully_disjoint_closed
    Metric.isClosed_sphere).mp (isConnected_sphere_full hd).isPreconnected
    U1 U2 hU1closed hU2closed hcov hdisj
  rcases hsep with h1 | h2
  · exact hkG1c (hkey G1 k (h1 (hx k)))
  · exact (hkey G1ᶜ j (h2 (hx j))) hjG1

end MeasureToMeasure.Leaves
