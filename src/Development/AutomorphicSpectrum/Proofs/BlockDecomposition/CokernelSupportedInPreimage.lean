module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinReesClosedSystem
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.GE.PSupp

theorem cokernel_supportedIn_preimage : ∀ {X : Scheme.{0}} (O : X.Opens) {P : X.Modules} {E : (O : Scheme.{0}).Modules}, P.IsQuasicoherent → E.IsQuasicoherent → ∀ f : P.restrict O.ι ⟶ E, Epi f → ∀ Bb : Subobject P, ∀ B : Subobject E, (B : (O : Scheme.{0}).Modules).IsQuasicoherent → (∀ (W : (O : Scheme.{0}).Opens), IsAffineOpen W → secs B W = (fun x => f.app W ((P.restrictAppIso O.ι W).inv x)) '' secs Bb (O.ι ''ᵁ W)) → ∀ (C : Set X), (∀ U : X.Opens, IsAffineOpen U → Disjoint (U : Set X) C → secs Bb U = Set.univ) → Scheme.Modules.SupportedIn (cokernel B.arrow) (O.ι.base ⁻¹' C) := by
  intro X O P E hP hE f hf Bb B hB hsec C hC
  haveI : P.IsQuasicoherent := hP
  haveI : E.IsQuasicoherent := hE
  haveI : Epi f := hf
  refine GlobalTheory.CompanionTheory.GE.Comb.supportedIn_of_secs_eq_univ hE hB fun W hW hd => ?_
  have hWi : IsAffineOpen (O.ι ''ᵁ W) := hW.image_of_isOpenImmersion O.ι
  have hdis : Disjoint ((O.ι ''ᵁ W : X.Opens) : Set X) C := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨y, hy, rfl⟩ hyC
    exact Set.disjoint_left.1 hd hy hyC
  rw [hsec W hW, hC _ hWi hdis, Set.image_univ]
  refine Function.Surjective.range_eq fun y => ?_
  obtain ⟨z, rfl⟩ := surjective_app_of_epi f hW y
  refine ⟨(P.restrictAppIso O.ι W).hom z, ?_⟩
  simp

end GlobalTheory.CompanionTheory.GE.PSupp
