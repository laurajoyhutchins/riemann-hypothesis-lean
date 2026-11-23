module

public import Mathlib.NumberTheory.NumberField.Basic
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
public import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.SetTheory.Cardinal.Rat
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

set_option autoImplicit false

namespace GlobalTheory.AlgClosedIsoOverNumberField

open Cardinal

theorem exists_ringEquiv_commutes (R K L : Type) [Field R] [Field K] [Field L] [IsAlgClosed K]
    [IsAlgClosed L] [Algebra R K] [Algebra R L] (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K) (hKL : #K = #L) :
    ∃ e : K ≃+* L, ∀ x : R, e (algebraMap R K x) = algebraMap R L x := by
  classical

  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis R L
  have hL : ℵ₀ < #L := hKL ▸ hK
  have hs' : #K = #s :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs hR hK
  have ht' : #L = #t :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hR hL
  obtain ⟨f⟩ : Nonempty (s ≃ t) := Cardinal.eq.1 (hs'.symm.trans (hKL.trans ht'))

  let := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis _ ht

  let e₀ : Algebra.adjoin R (Set.range ((↑) : s → K)) ≃ₐ[R]
      Algebra.adjoin R (Set.range ((↑) : t → L)) :=
    hs.1.aevalEquiv.symm.trans ((MvPolynomial.renameEquiv R f).trans ht.1.aevalEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv K L e₀.toRingEquiv, fun x => ?_⟩
  rw [IsScalarTower.algebraMap_apply R (Algebra.adjoin R (Set.range ((↑) : s → K))) K,
    IsAlgClosure.equivOfEquiv_algebraMap, AlgEquiv.coe_ringEquiv,
    AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]

theorem exists_ringEquiv_comp_eq :
    ∀ (K Ω₁ Ω₂ : Type) [Field K] [NumberField K] [Field Ω₁] [Field Ω₂] [IsAlgClosed Ω₁]
      [IsAlgClosed Ω₂] [CharZero Ω₁] [CharZero Ω₂] (a : K →+* Ω₁) (b : K →+* Ω₂),
      Cardinal.mk Ω₁ = Cardinal.mk Ω₂ → Cardinal.aleph0 < Cardinal.mk Ω₁ →
        ∃ ι : Ω₁ ≃+* Ω₂, ∀ x, ι (a x) = b x := by
  intro K Ω₁ Ω₂ _ _ _ _ _ _ _ _ a b hcard hbig
  let : Algebra K Ω₁ := a.toAlgebra
  let : Algebra K Ω₂ := b.toAlgebra

  have hK : #K ≤ ℵ₀ := by
    have := Algebra.IsAlgebraic.cardinalMk_le_max ℚ K
    rwa [Cardinal.mkRat, max_self] at this
  obtain ⟨e, he⟩ := exists_ringEquiv_commutes K Ω₁ Ω₂ hK hbig hcard
  exact ⟨e, he⟩

end GlobalTheory.AlgClosedIsoOverNumberField
