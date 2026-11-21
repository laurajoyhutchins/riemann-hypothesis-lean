-- Experimental root: same five proposition types and witnesses as Main.lean,
-- but omits additional modules imported by MainTheoremsAll.
-- This file does not replace Main.lean or certify a successful build.
import Statements
import Supplements.Kernels.MainTheorems

theorem riemannHypothesis_minimal : RiemannHypothesis := rhOfAll

theorem riemannZeta_eq_zero_re_minimal : RiemannZetaZerosOnLine := rhOfAll

theorem LFunction_ne_zero_of_half_lt_re_minimal : DirichletLNonvanishingRightOfHalf := allChi

theorem LFunction_eq_zero_re_minimal : DirichletLZerosOnLine := claimAll.2.1

theorem LFunction_eq_zero_re_of_isPrimitive_minimal : PrimitiveDirichletLZerosOnLine := critAll
