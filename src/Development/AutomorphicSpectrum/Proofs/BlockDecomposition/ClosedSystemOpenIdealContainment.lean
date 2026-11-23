module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSubsetSupportProper
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CokernelSupportedInPreimage
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsQuasicoherentOfSecsImage
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemOfBadSetClosedFibre
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionsEqUnivOffBadSupportStatement
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

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.PSupp

theorem propSupp_of_closed_image : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (O : X.Opens), letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩; ∀ {P : X.Modules} {E : (O : Scheme.{0}).Modules}, IsCoherent P → IsCoherent E → ∀ f : P.restrict O.ι ⟶ E, Epi f → ∀ (Sb : Subobject P) (T : (O : Scheme.{0}).IdealSheafData), IsClosed (O.ι '' (T.support : Set (O : Scheme.{0}))) → (∀ V : X.Opens, Disjoint (V : Set X) (O.ι '' (T.support : Set (O : Scheme.{0}))) → secs Sb V = Set.univ) → ∀ Bb : Subobject P, (Bb : X.Modules).IsQuasicoherent → Bb ⊔ powSub I P 1 = Sb → ∀ B : Subobject E, (∀ (W : (O : Scheme.{0}).Opens), IsAffineOpen W → secs B W = (fun x => f.app W ((P.restrictAppIso O.ι W).inv x)) '' secs Bb (O.ι ''ᵁ W)) → PropSupp A B := by
  intro A _ _ I hI X _ _ O
  letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩
  intro P E hP hE f hf Sb T hTc hSb Bb hBq hBS B hB
  have hC : IsClosed (badSet Bb) := isClosed_badSet Bb
  have hCO : badSet Bb ⊆ (O : Set X) := subset_of_closedFibre I hI O (badSet Bb) hC
    (fun x hx hIx => by
      obtain ⟨y, _, rfl⟩ := mem_of_badSet_closedFibre I hP Bb hBq _ hTc
        (fun V hV => by rw [hBS]; exact hSb V hV) x hx hIx
      rw [← Scheme.Opens.range_ι O]
      exact ⟨y, rfl⟩)
  obtain ⟨T', hT'supp, hT'prop⟩ := ClosedSub.closed_subset_support_proper (A := A) O (badSet Bb) hC hCO
  have hBqc := isQuasicoherent_of_secs_image O hP.1 hE.1 f Bb hBq B hB
  refine ⟨T', hT'prop, ?_⟩
  rw [hT'supp]
  exact cokernel_supportedIn_preimage O hP.1 hE.1 f hf Bb B hBqc hB (badSet Bb)
    (fun U hU hd => GlobalTheory.T.sections_eq_univ_off_bad_support hP.1 Bb hBq U hU hd)

end GlobalTheory.CompanionTheory.GE.PSupp
