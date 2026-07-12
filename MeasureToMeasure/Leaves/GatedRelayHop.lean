import MeasureToMeasure.Leaves.GatedChainUnion

/-!
# Two chains bridged across a cell boundary (`prop_2_2` Stage 3 relay, leaf 4 piece 4)

`gated_chainUnion_retention_bounded` retains mass along ONE chain confined to a single region. The
Voronoi-adjacency relay (Stage 3 item 3) needs TWO chains run in sequence: a "connector" chain
confined to a cell `C`, followed by a "straddle" chain crossing a boundary point `y' ∉ C` into the
next cell. This leaf composes the two retention guarantees into one, closing the radius tension
documented in the `prop-2-2-steps-2-3-campaign` project notes (a dispatched research fork proved the
OLD architecture -- both chains built with opaque, independently-derived radii -- is a scale-invariant
impossibility: no choice of radius or extraction point lets a straddle ball simultaneously contain the
connector's endpoint and avoid the connector's own tail).

**The fix, not a patch.** The straddle chain (built via `exists_geodesicConvex_arc_chain_inner_ball`,
`VoronoiStraddle.lean`) has an EXPLICIT, KNOWN radius `ρ0/2` at every point -- not an opaque one
extracted from `exists_uniform_margin`. Combined with the elementary fact that the connector chain's
own LAST ball, being confined to `C ∌ y'`, is forced to have radius `≤ geodesicDist y' (last center)`
(a direct contrapositive of ball membership, no compactness needed), choosing the connector's own
closeness-to-`y'` parameter smaller than `ρ0/2` forces the connector's last ball INSIDE the straddle
chain's first ball -- with no disjointness needed between the two chains at all. The straddle chain's
own `gated_chainUnion_retention_bounded` application (run on the measure ALREADY evolved by the
connector's schedule) then carries the connector's retained mass straight through.

This lemma is stated generically over the confining region `C` (not tied to `voronoiCell`), since
nothing in the argument is Voronoi-specific -- only "a chain confined to a region not containing the
crossing point" matters.
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory Set
open scoped ENNReal
open MeasureToMeasure

variable {d : ℕ}

/-- **Two chains bridged: a confined chain followed by a ball-crossing chain.** Chain 1 (`z₁`,
length `n₁`) is confined to a region `C` not containing `y'`; chain 2 (`z₂`, length `n₂`) starts
exactly where chain 1 ends and is confined to `geodesicBall y' ρ0` with the EXPLICIT radius `ρ0/2`.
Given chain 1's endpoint is within `ρ0/2` of `y'` (`hqclose`), its own last-ball radius is forced
`≤ ρ0/2` too (`hRad₁n₁le`, since that ball is confined to `C ∌ y'`, so `y'` sits outside it) --
putting chain 1's last ball INSIDE chain 2's first ball, so `gated_chainUnion_retention_bounded`
applied to chain 2 (on the ALREADY-EVOLVED measure after chain 1's schedule) carries chain 1's
retained mass straight through. No disjointness is needed between the two chains at all. -/
theorem gated_relay_hop_retention {C : Set (Eucl d)}
    (μ : Measure (Eucl d)) [IsProbabilityMeasure μ] (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (n₁ : ℕ) (z₁ : ℕ → Eucl d) (Rad₁ : ℕ → ℝ)
    (hz₁ : ∀ t, z₁ t ∈ sphere d) (hRad₁ : ∀ t, Rad₁ t ∈ Set.Ioo 0 (Real.pi / 2))
    (hsub₁ : ∀ t, geodesicBall (z₁ t) (Rad₁ t) ⊆ C)
    (hchain₁ : ∀ t < n₁,
      (geodesicBall (z₁ t) (Rad₁ t) ∩ geodesicBall (z₁ (t + 1)) (Rad₁ (t + 1))).Nonempty)
    (hdisj₁ : ∀ a b, a + 2 ≤ b → b ≤ n₁ →
      Disjoint (geodesicBall (z₁ a) (Rad₁ a)) (geodesicBall (z₁ b) (Rad₁ b)))
    {y' : Eucl d} (hy's : y' ∈ sphere d) (hy'notin : y' ∉ C) {ρ0 : ℝ}
    (hρ0 : ρ0 ∈ Set.Ioo 0 (Real.pi / 2))
    (hqclose : geodesicDist y' (z₁ n₁) < ρ0 / 2)
    (n₂ : ℕ) (z₂ : ℕ → Eucl d)
    (hz₂0 : z₂ 0 = z₁ n₁)
    (hz₂ : ∀ t, z₂ t ∈ sphere d)
    (_hsub₂ : ∀ t, geodesicBall (z₂ t) (ρ0 / 2) ⊆ geodesicBall y' ρ0)
    (hchain₂ : ∀ t < n₂,
      (geodesicBall (z₂ t) (ρ0 / 2) ∩ geodesicBall (z₂ (t + 1)) (ρ0 / 2)).Nonempty)
    (hdisj₂ : ∀ a b, a + 2 ≤ b → b ≤ n₂ →
      Disjoint (geodesicBall (z₂ a) (ρ0 / 2)) (geodesicBall (z₂ b) (ρ0 / 2))) :
    ∃ θ : Params d, switches θ ≤ n₁ + n₂ ∧
      (1 - ENNReal.ofReal ε) ^ (n₁ + n₂) * μ (⋃ j ≤ n₁, geodesicBall (z₁ j) (Rad₁ j)) ≤
        Axioms.measureFlow θ T μ (geodesicBall (z₂ n₂) (ρ0 / 2)) := by
  obtain ⟨θ₁, hsw₁, hmass₁, hfix₁⟩ :=
    gated_chainUnion_retention_bounded μ T ε hT hε n₁ z₁ hz₁ Rad₁ hRad₁ hchain₁ hdisj₁
  haveI := Axioms.isProbabilityMeasure_measureFlow θ₁ T μ
  have hRad₁n₁le : Rad₁ n₁ ≤ ρ0 / 2 := by
    by_contra hcon
    push Not at hcon
    have hy'mem : y' ∈ geodesicBall (z₁ n₁) (Rad₁ n₁) :=
      ⟨hy's, by rw [geodesicDist_comm]; linarith [hqclose]⟩
    exact hy'notin (hsub₁ n₁ hy'mem)
  have hballsub : geodesicBall (z₁ n₁) (Rad₁ n₁) ⊆ geodesicBall (z₂ 0) (ρ0 / 2) := by
    rw [hz₂0]
    intro w hw
    exact ⟨hw.1, lt_of_lt_of_le hw.2 hRad₁n₁le⟩
  have hRad₂ : ∀ t : ℕ, (ρ0 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun _ => ⟨half_pos hρ0.1, by linarith [hρ0.2, Real.pi_pos]⟩
  obtain ⟨θ₂, hsw₂, hmass₂, hfix₂⟩ :=
    gated_chainUnion_retention_bounded (Axioms.measureFlow θ₁ T μ) T ε hT hε n₂ z₂ hz₂
      (fun _ => ρ0 / 2) hRad₂ hchain₂ hdisj₂
  refine ⟨Axioms.comp θ₁ θ₂, ?_, ?_⟩
  · exact (Axioms.switches_comp θ₁ θ₂).trans (Nat.add_le_add hsw₁ hsw₂)
  · rw [Axioms.measureFlow_comp]
    have hunion0 : geodesicBall (z₂ 0) (ρ0 / 2) ⊆ ⋃ j ≤ n₂, geodesicBall (z₂ j) (ρ0 / 2) := by
      intro w hw
      simp only [Set.mem_iUnion]
      exact ⟨0, Nat.zero_le n₂, hw⟩
    have hstepB : Axioms.measureFlow θ₁ T μ (geodesicBall (z₁ n₁) (Rad₁ n₁)) ≤
        Axioms.measureFlow θ₁ T μ (⋃ j ≤ n₂, geodesicBall (z₂ j) (ρ0 / 2)) := by
      gcongr
      exact hballsub.trans hunion0
    have hchain12 : (1 - ENNReal.ofReal ε) ^ n₁ * μ (⋃ j ≤ n₁, geodesicBall (z₁ j) (Rad₁ j)) ≤
        Axioms.measureFlow θ₁ T μ (⋃ j ≤ n₂, geodesicBall (z₂ j) (ρ0 / 2)) :=
      hmass₁.trans hstepB
    calc (1 - ENNReal.ofReal ε) ^ (n₁ + n₂) * μ (⋃ j ≤ n₁, geodesicBall (z₁ j) (Rad₁ j))
        = (1 - ENNReal.ofReal ε) ^ n₂ *
            ((1 - ENNReal.ofReal ε) ^ n₁ * μ (⋃ j ≤ n₁, geodesicBall (z₁ j) (Rad₁ j))) := by
          rw [pow_add]; ring
      _ ≤ (1 - ENNReal.ofReal ε) ^ n₂ *
            Axioms.measureFlow θ₁ T μ (⋃ j ≤ n₂, geodesicBall (z₂ j) (ρ0 / 2)) := by gcongr
      _ ≤ Axioms.measureFlow θ₂ T (Axioms.measureFlow θ₁ T μ) (geodesicBall (z₂ n₂) (ρ0 / 2)) :=
          hmass₂

end MeasureToMeasure.Leaves
