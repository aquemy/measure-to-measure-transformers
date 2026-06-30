-- Root module for the MeasureToMeasure formalization.
-- Re-exports the foundations, axiom layer, and kernel-checked leaves.
import MeasureToMeasure.Foundations.Sphere
import MeasureToMeasure.Foundations.Projector
import MeasureToMeasure.Foundations.GeodesicDistance
import MeasureToMeasure.Axioms.Wasserstein
import MeasureToMeasure.Axioms.ContinuityEquation
import MeasureToMeasure.Leaves.SeparatingHyperplane
import MeasureToMeasure.Leaves.BallChain
import MeasureToMeasure.Leaves.Lyapunov
import MeasureToMeasure.Leaves.GateODE
import MeasureToMeasure.Leaves.BarycenterODE
import MeasureToMeasure.Leaves.Pigeonhole
import MeasureToMeasure.Leaves.Coupling
import MeasureToMeasure.Leaves.GeodesicGradient
