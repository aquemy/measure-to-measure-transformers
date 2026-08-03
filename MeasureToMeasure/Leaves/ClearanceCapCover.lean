import MeasureToMeasure.Foundations.Sphere

/-!
# Leaves (lemma 3.3 campaign): the clearance cap cover

Geometry feeding the overlap-tolerant staging engine `staged_prefix_overlapping_caps`
(`OverlapStagingInduction.lean`): from finitely many small, well-separated compact clusters of the
acted supports, produce the full cap/gate/staged-ball bundle the engine consumes, with every gate
ball clear of the bystander region `F` and every staged ball inside its gate.

## Why one enclosing cap per cluster, not a fine subcover

The plan's first sketch for this leaf was a fine finite subcover with `TunedCapSystem`-style radius
tuning. That shape is PROVABLY unusable for the exact-full-mass conclusion this campaign needs, by
the dead-annulus fact already on record in F35's scope note (RESEARCH.md): the thin gate annuli
`ball (c j) (b j) \ closedBall (c j) (a j)` are genuine per-block dead zones, and the engine's
`hEann` obligation makes every LATER cell avoid every EARLIER annulus. Consequently a support point
lying in the first-fired cap's annulus belongs to no admissible cell at all: it is outside that
cap's own cell (`hE` confines cells to collapse balls) and excluded from every later cell
(`hEann`). Exact coverage therefore forces, cap by cap, the support's trace on each gate ball into
that cap's own collapse ball, up to earlier collapse balls:

  `S ∩ (ball (c j) (b j) \ closedBall (c j) (a j)) ⊆ ⋃ (k < j), closedBall (c k) (a k)`.

For the FIRST cap the right side is empty, so its annulus must miss `S` entirely. A support that
is radially spread around every candidate centre (any fat connected `S`) has an interval distance
profile from every centre, so a sub-diameter cap always has a nonempty annulus trace: the first
cap must wholly enclose its component of `S`. The honest cover shape is therefore ONE enclosing
cap per small cluster, with the gate clearing both the other clusters (which makes every annulus
trace on `S` empty, discharging `hEann` outright) and the bystander region (which keeps bystander
measures gate-null, hence exactly fixed). No off-finite-bad-set radius tuning is needed once each
cluster is wholly inside its collapse ball: the radii are explicit (`a = r`, `b = 2r`, `ρ = r/2`)
and the `hsep` staging dichotomy always takes its clear branch.

## Interface wiring (for the g5 assembly)

* `δ0` and `hclear` are exactly what `geodesicHullSet_clearance` (`GeodesicHullSet.lean`) provides:
  cluster points are unit vectors of the support union, hence hull members by
  `mem_geodesicHullSet_self`, and every `δ0`-ball centred in the hull misses the closed bystander
  union `F`.
* The conclusions are, in order, the engine's `hc`/`ha`/`hab`/`hb2` bundle, the cells (the
  clusters themselves) inside their collapse balls (`hE`), the annulus avoidance (`hEann`, proved
  from whole-gate clearance), the staging radius `ρ` with the wholly-in-or-wholly-out dichotomy
  (`hsep`), gate disjointness from `F` (bystander fixing), and staged-ball positioning (inside
  gates, pairwise disjoint, centred at support points, i.e. inside the hull) for the corridor
  phase.
* Scope, on the record: clusters of diameter beyond the bystander clearance margin are genuinely
  out of reach of this block family (F35 scope note); `hdiam`/`hgap`/`hδ0` are the honest
  quantitative expression of that limit, not a convenience.
-/

namespace MeasureToMeasure.Leaves

open MeasureToMeasure

variable {d : ℕ}

/-- **The clearance cap cover.** From finitely many nonempty clusters `K i` on the sphere (no
compactness needed: only the pointwise bounds enter), each of diameter at most `r`, pairwise
`3r`-separated,
with every `δ0`-ball centred in a cluster clear of the bystander region `F` (`2r ≤ δ0`): one
enclosing cap per cluster (centre `c k ∈ K k`, collapse radius `a k = r`, gate radius `b k = 2r`)
and a staging radius `ρ = r/2` satisfying the full `staged_prefix_overlapping_caps` bundle. Every
annulus trace on the clusters is empty (later clusters clear earlier gates wholly), the staging
dichotomy always takes its clear branch, every gate ball misses `F`, and the staged balls are
pairwise disjoint and sit inside their gates at support-point centres. -/
theorem exists_clearance_cap_cover {n : ℕ} {K : Fin n → Set (Eucl d)} {F : Set (Eucl d)}
    {r δ0 : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hKs : ∀ i, K i ⊆ sphere d) (hKne : ∀ i, (K i).Nonempty)
    (hdiam : ∀ i, ∀ x ∈ K i, ∀ y ∈ K i, dist x y ≤ r)
    (hgap : ∀ i k : Fin n, i ≠ k → ∀ x ∈ K i, ∀ y ∈ K k, 3 * r ≤ dist x y)
    (hδ0 : 2 * r ≤ δ0)
    (hclear : ∀ i, ∀ x ∈ K i, Disjoint (Metric.ball x δ0) F) :
    ∃ (c : Fin n → Eucl d) (a b : Fin n → ℝ) (ρ : ℝ),
      (∀ k, c k ∈ K k) ∧ (∀ k, c k ∈ sphere d) ∧
      (∀ j k : Fin n, j ≠ k → c j ≠ c k) ∧
      (∀ k, 0 < a k) ∧ (∀ k, a k < b k) ∧ (∀ k, b k ≤ 2) ∧ (∀ k, b k ≤ δ0) ∧
      (∀ k, K k ⊆ Metric.closedBall (c k) (a k)) ∧
      (∀ j k : Fin n, j < k →
        Disjoint (K k) (Metric.ball (c j) (b j) \ Metric.closedBall (c j) (a j))) ∧
      0 < ρ ∧ ρ ≤ r ∧
      (∀ j k : Fin n, j < k →
        dist (c j) (c k) + ρ ≤ a k ∨ b k + ρ ≤ dist (c j) (c k)) ∧
      (∀ k, Disjoint (Metric.ball (c k) (b k)) F) ∧
      (∀ k, Metric.ball (c k) ρ ⊆ Metric.ball (c k) (b k)) ∧
      (∀ j k : Fin n, j ≠ k →
        Disjoint (Metric.closedBall (c j) ρ) (Metric.closedBall (c k) ρ)) := by
  choose c hc using hKne
  have hcd : ∀ j k : Fin n, j ≠ k → 3 * r ≤ dist (c j) (c k) := fun j k hjk =>
    hgap j k hjk (c j) (hc j) (c k) (hc k)
  refine ⟨c, fun _ => r, fun _ => 2 * r, r / 2,
    fun k => hc k, fun k => hKs k (hc k), ?_, fun _ => hr, fun _ => by linarith,
    fun _ => by linarith, fun _ => hδ0, ?_, ?_, by positivity, by linarith, ?_, ?_, ?_, ?_⟩
  · -- distinct centres
    intro j k hjk heq
    have h1 := hcd j k hjk
    rw [heq, dist_self] at h1
    linarith
  · -- each cluster sits inside its own collapse ball
    intro k x hx
    exact Metric.mem_closedBall.mpr (hdiam k x hx (c k) (hc k))
  · -- later clusters clear earlier annuli: they clear the whole earlier gate ball
    intro j k hjk
    refine Set.disjoint_left.mpr fun y hy hyann => ?_
    have h1 : 3 * r ≤ dist y (c j) := hgap k j (ne_of_lt hjk).symm y hy (c j) (hc j)
    have h2 : dist y (c j) < 2 * r := Metric.mem_ball.mp hyann.1
    linarith
  · -- staging dichotomy: distinct caps always take the clear branch
    intro j k hjk
    right
    have h1 := hcd j k (ne_of_lt hjk)
    linarith
  · -- gate balls clear the bystander region
    intro k
    exact Set.disjoint_of_subset_left (Metric.ball_subset_ball hδ0) (hclear k (c k) (hc k))
  · -- staged balls sit inside their gates
    intro k
    exact Metric.ball_subset_ball (by linarith)
  · -- staged balls are pairwise disjoint
    intro j k hjk
    refine Set.disjoint_left.mpr fun z hzj hzk => ?_
    have h1 := hcd j k hjk
    have h2 : dist z (c j) ≤ r / 2 := Metric.mem_closedBall.mp hzj
    have h3 : dist z (c k) ≤ r / 2 := Metric.mem_closedBall.mp hzk
    have h4 := dist_triangle (c j) z (c k)
    rw [dist_comm (c j) z] at h4
    linarith

end MeasureToMeasure.Leaves
