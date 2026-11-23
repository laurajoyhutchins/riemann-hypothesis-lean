module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderInductionInjectiveStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteOpenHopfOrderStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemBtOrderIffBtSetStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularFunctionIffSectionStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem GlobalTheory.CompanionTheory.Ar.BT.btOrder_isHopfOrder_of_finOpenSub :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → IsHopfOrder (Γ.btOrder U) := by
  intro R _ _ _ T _ _ Γ U hU
  obtain ⟨H, A, hH, hA, hAf⟩ := GlobalTheory.T.finite_open_hopf_order R T Γ U hU
  have key : Γ.btOrder U = indOrder H.subtype A := by
    ext f
    rw [GlobalTheory.T.mem_btOrder_iff_btSet R T Γ U f]
    constructor
    · intro hf t
      obtain ⟨s, hs⟩ := (GlobalTheory.T.regular_function_iff_section R T Γ U _).1 (hf t)
      exact (hAf _).2 ⟨s, fun t' h => hs t' h⟩
    · intro hf t
      refine (GlobalTheory.T.regular_function_iff_section R T Γ U _).2 ?_
      obtain ⟨s, hs⟩ := (hAf _).1 (hf t)
      exact ⟨s, fun t' h => hs ⟨t', (hH t').2 h⟩ h⟩
  rw [key]
  exact GlobalTheory.T.hopf_order_induction_injective R T H H.subtype H.subtype_injective A hA
