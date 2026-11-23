module

public import Mathlib.RingTheory.KrullDimension.Basic
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
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.MvPolynomial.Eval

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial

namespace BaseChangeMin

variable {σ : Type*} [Fintype σ] {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']

section GD

attribute [local instance] MvPolynomial.algebraMvPolynomial



end GD

theorem ringKrullDim_quotient_le_of_minimalPrimes {R : Type*} [CommRing R] (I : Ideal R)
    {N : WithBot ℕ∞} (h : ∀ Z ∈ I.minimalPrimes, ringKrullDim (R ⧸ Z) ≤ N) :
    ringKrullDim (R ⧸ I) ≤ N := by
  rw [ringKrullDim_quotient, Order.krullDim_eq_iSup_coheight, iSup_le_iff]
  intro a
  obtain ⟨Z, hZ, hZa⟩ :=
    Ideal.exists_minimalPrimes_le ((PrimeSpectrum.mem_zeroLocus _ _).mp a.2)
  have : Z.IsPrime := hZ.1.1
  let z : PrimeSpectrum.zeroLocus (R := R) (I : Set R) :=
    ⟨⟨Z, inferInstance⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr hZ.1.2⟩
  have hza : z ≤ a := hZa
  let e : Set.Ici z ↪o PrimeSpectrum.zeroLocus (R := R) (Z : Set R) :=
    OrderEmbedding.ofMapLEIff
      (fun x => ⟨x.1.1, (PrimeSpectrum.mem_zeroLocus _ _).mpr (show Z ≤ x.1.1.asIdeal from x.2)⟩)
      fun _ _ => Iff.rfl
  calc ((Order.coheight a : ℕ∞) : WithBot ℕ∞) ≤ ((Order.coheight z : ℕ∞) : WithBot ℕ∞) :=
        WithBot.coe_le_coe.mpr (Order.coheight_anti hza)
    _ = Order.krullDim (Set.Ici z) := Order.coheight_eq_krullDim_Ici z
    _ ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R := R) (Z : Set R)) :=
        Order.krullDim_le_of_orderEmbedding e
    _ = ringKrullDim (R ⧸ Z) := (ringKrullDim_quotient Z).symm
    _ ≤ N := h Z hZ

end BaseChangeMin

end GroundTheory.Heights₂.Heights.Targets
