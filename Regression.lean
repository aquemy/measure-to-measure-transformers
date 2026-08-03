-- Root module for the refutation regression suite (MUST-PASS half).
-- `Regression/Refuted/` holds kernel-checked disproofs of historical false axiom statements;
-- `Regression/NonVacuity/` holds per-axiom witnesses. The MUST-FAIL half lives in `Refutations/`
-- (not a build target; checked by `scripts/refutation-gate.sh`).
import Regression.OldStatements
import Regression.Refuted.F11_LemmaThreeFour
import Regression.Refuted.F11_LemmaFiveOne
import Regression.Refuted.F12_Volume
import Regression.Refuted.F12_ClusterToPoint
import Regression.Refuted.F12_HeavyTails
import Regression.Refuted.F14_IdenticalInputs
import Regression.Refuted.F18_DimOne
import Regression.Refuted.F26_HeavyTailsNoAtoms
import Regression.Refuted.F31_Lemma54DimensionFree
import Regression.Refuted.F33_ParkedScheduleNegativeT
import Regression.Refuted.CapMassNonzeroNearBallDraft
import Regression.Refuted.AsymmetricCapFromUnflowedSupport
import Regression.Refuted.HgenRestUnconditionallyFalse
import Regression.Refuted.HuUnitBarycenterStrictConvexity
import Regression.Refuted.Lemma33NoUniversalMap
import Regression.NonVacuity.MidLevel
import Regression.NonVacuity.MainResults
import Regression.NonVacuity.AsymmetricMassGapCap
import Regression.NonVacuity.DisentangleResolvingAsym
import Regression.NonVacuity.DisentangleAvoidingInsert
import Regression.NonVacuity.Lemma33CapSeparation
import Regression.NonVacuity.DisentangleAssembly
import Regression.NonVacuity.MergeTolerantRelocation
import Regression.NonVacuity.Lemma54
import Regression.NonVacuity.ParkedSchedule
