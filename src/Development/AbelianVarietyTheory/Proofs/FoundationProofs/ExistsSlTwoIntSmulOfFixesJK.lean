module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

noncomputable section

namespace GlobalTheory.KZ.ES.JStab

theorem eps_eOm_of_alg {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (x : ℚ) : ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hε : Function.Injective ε := ε.injective
  unfold eOm
  apply Function.invFun_eq
  haveI : NeZero (x.den : Ω) := ⟨by exact_mod_cast x.den_nz⟩
  obtain ⟨ζ, hζ0⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic x.den Ω)
    (by rw [Polynomial.degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.2 x.den_pos).ne')
  have hζ : IsPrimitiveRoot ζ x.den := (Polynomial.isRoot_cyclotomic_iff).1 hζ0
  have hζ' : IsPrimitiveRoot (ε ζ) x.den := hζ.map_of_injective hε
  haveI : NeZero x.den := ⟨x.den_nz⟩
  have hpow : (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨x.num, ?_⟩
    have hx : (x : ℂ) * x.den = x.num := by exact_mod_cast Rat.mul_den_eq_num x
    calc (x.den : ℂ) * (2 * Real.pi * Complex.I * (x : ℂ)) = ((x : ℂ) * x.den) * (2 * Real.pi * Complex.I) := by ring
      _ = _ := by rw [hx]
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hpow
  exact ⟨ζ ^ i, by rw [map_pow, hi]⟩

theorem eOm_ne_zero' {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (x : ℚ) :
    eOm ε x ≠ 0 := by
  intro h0
  have := eps_eOm_of_alg ε x
  rw [h0, map_zero] at this
  exact Complex.exp_ne_zero _ this.symm

end GlobalTheory.KZ.ES.JStab
