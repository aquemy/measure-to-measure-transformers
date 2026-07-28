import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import MeasureToMeasure.Foundations.Sphere

/-!
# Leaf (lemma 5.4 campaign, G4): compact cores of measurable sets under a finite measure

The paper's Section 5 approximation argument implicitly uses a Lusin-type step: replace each
finite-range preimage cell by a compact core carrying all but an arbitrarily small amount of its
mass. `Eucl d` is a Polish space and every finite Borel measure on it is inner regular on
measurable sets, so this is a thin wrapper over Mathlib's
`MeasurableSet.exists_isCompact_sdiff_lt`.

We record the plain version and the sphere-restricted version (cells of a map defined on the
sphere live inside `sphere d`, and their compact cores then do too, which is what the Phase-1
cap-system construction downstream consumes).
-/

namespace MeasureToMeasure.Leaves

open MeasureTheory

variable {d : ℕ}

/-- **Compact core of a measurable set.** Under a finite Borel measure on `Eucl d`, every
measurable set `A` contains a compact `K` with leftover mass `μ (A \ K)` below any prescribed
positive budget `η`. Inner regularity of finite measures on the Polish space `Eucl d`. -/
theorem exists_compact_core (μ : Measure (Eucl d)) [IsFiniteMeasure μ]
    (A : Set (Eucl d)) (hA : MeasurableSet A) (η : ENNReal) (hη : 0 < η) :
    ∃ K, IsCompact K ∧ K ⊆ A ∧ μ (A \ K) < η := by
  obtain ⟨K, hKA, hKc, hKlt⟩ :=
    hA.exists_isCompact_sdiff_lt (measure_ne_top μ A) hη.ne'
  exact ⟨K, hKc, hKA, hKlt⟩

/-- **Compact core inside the sphere.** If the measurable set `A` lives on the unit sphere, so
does its compact core. This is the form the finite-range preimage cells of a sphere-valued map
need. -/
theorem exists_compact_core_subset_sphere (μ : Measure (Eucl d)) [IsFiniteMeasure μ]
    (A : Set (Eucl d)) (hA : MeasurableSet A) (hAs : A ⊆ sphere d)
    (η : ENNReal) (hη : 0 < η) :
    ∃ K, IsCompact K ∧ K ⊆ A ∧ K ⊆ sphere d ∧ μ (A \ K) < η := by
  obtain ⟨K, hKc, hKA, hKlt⟩ := exists_compact_core μ A hA η hη
  exact ⟨K, hKc, hKA, hKA.trans hAs, hKlt⟩

end MeasureToMeasure.Leaves
