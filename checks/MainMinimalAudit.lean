import Main
import MainMinimal

-- Exact proof-checking is performed by the pinned Lean kernel when these
-- declarations and their dependencies elaborate and compile.
-- The audit output MUST be retained before calling this experiment verified.
#check riemannHypothesis
#check riemannHypothesis_minimal
#check riemannZeta_eq_zero_re
#check riemannZeta_eq_zero_re_minimal
#check LFunction_ne_zero_of_half_lt_re
#check LFunction_ne_zero_of_half_lt_re_minimal
#check LFunction_eq_zero_re
#check LFunction_eq_zero_re_minimal
#check LFunction_eq_zero_re_of_isPrimitive
#check LFunction_eq_zero_re_of_isPrimitive_minimal

#print axioms riemannHypothesis
#print axioms riemannHypothesis_minimal
#print axioms riemannZeta_eq_zero_re
#print axioms riemannZeta_eq_zero_re_minimal
#print axioms LFunction_ne_zero_of_half_lt_re
#print axioms LFunction_ne_zero_of_half_lt_re_minimal
#print axioms LFunction_eq_zero_re
#print axioms LFunction_eq_zero_re_minimal
#print axioms LFunction_eq_zero_re_of_isPrimitive
#print axioms LFunction_eq_zero_re_of_isPrimitive_minimal
