/-!
Source-level proof gate for the four Harris–Taylor proof-sharing edits.

Successful compilation checks elaboration of the real source dependencies.
This is not a check of the five final RH theorem types or independent replay
of a newly generated full kernel export.
-/
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsGluedFirstOrderDeformation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackAlong

#check GlobalTheory.UPel.HT.exists_sqZero_lift_of_fil
#check GlobalTheory.HTGlue.exists_obj_of_summand
#check GlobalTheory.HTPullEvery.exists_objMap
#check GlobalTheory.UPel.HT.BaseChange.exists_objMap
#check GlobalTheory.HTPull.exists_objMap_pull
#check GlobalTheory.UPel.HT.Pull.exists_objMap
#print axioms GlobalTheory.HTGlue.exists_obj_of_summand
#print axioms GlobalTheory.UPel.HT.BaseChange.exists_objMap
#print axioms GlobalTheory.HTPull.exists_objMap_pull
#print axioms GlobalTheory.UPel.HT.Pull.exists_objMap
