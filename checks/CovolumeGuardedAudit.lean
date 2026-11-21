-- The audited module is deliberately not imported by Main.
-- A successful run of this file requires a real Lean elaboration of the
-- generic theorem and both exact-type specializations.
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CovolumeGuardedAssembly
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CovolXOfSteps

open GlobalTheory.CovTop
open GlobalTheory.CovTop.Assembly

-- These are the existing public theorem statements; the two added lemmas
-- must elaborate to the same statement types.
#check covolX_of_steps
#check covolX_of_steps_from_guard
#check covolX_of_lift_bounds_and_coreLe
#check covolX_of_lift_bounds_from_guard

-- Inspect differences in transitive trust dependencies before replacing
-- the original proof bodies with the generic specializations.
#print axioms covolX_of_steps
#print axioms covolX_of_steps_from_guard
#print axioms covolX_of_lift_bounds_and_coreLe
#print axioms covolX_of_lift_bounds_from_guard

-- The type of each new theorem already asserts all eight hypotheses and
-- the exact old result type, so no reinterpretation of a theorem is needed.
