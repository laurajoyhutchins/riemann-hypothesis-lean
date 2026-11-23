module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.SplitEq
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GlobalTheory.DiscSpec
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

theorem UpperTheory.V.KernelIndexFullLattice.quotMk_holds :
    UpperTheory.V.KernelIndexFullLattice.QuotMk := by
  intro E _ _ _ a g
  have h0 : mk (latticeGL E a) (Quotient.out (mk (latticeGL E a) g)) = mk (latticeGL E a) g :=
    Quotient.out_eq _
  obtain ⟨⟨l, hl⟩, e⟩ := mk_eq_iff.1 h0.symm
  obtain ⟨γ, n, rfl⟩ := mem_latticeGL_iff.1 hl
  have hγ1 : AdelicGLn.diagonal E a γ ∈ Reduction.normOneGL (K := E) (n := a) := Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩
  have hγΓ : (⟨AdelicGLn.diagonal E a γ, hγ1⟩ : Reduction.normOneGL (K := E) (n := a)) ∈ UpperTheory.V.KernelIndexFullLattice.Γ1 E a := ⟨γ, rfl⟩
  have h1 : retractOne (ratGL E a γ * splitCentre E a 1 ^ n * g) =
      (⟨AdelicGLn.diagonal E a γ, hγ1⟩ : Reduction.normOneGL (K := E) (n := a)) * retractOne g := by
    have h2 := retractOne_coe_mul (⟨AdelicGLn.diagonal E a γ, hγ1⟩ : Reduction.normOneGL (K := E) (n := a))
      (splitCentre E a 1 ^ n * g)
    have h3 : retractOne (K := E) (n := a) (splitCentre E a 1 ^ n * g) = retractOne g := by
      rw [← splitCentre_intCast, UpperTheory.V.KernelIndexFullLattice.splitEq_holds, retractOne_mul, retractOne_centralSection, one_mul]
    rw [h3] at h2
    rw [mul_assoc]
    exact h2
  unfold UpperTheory.V.KernelIndexFullLattice.quotMap
  rw [← e]
  exact (congrArg _ h1).trans (RightCosetSpace.mk_mul_of_mem hγΓ _)
