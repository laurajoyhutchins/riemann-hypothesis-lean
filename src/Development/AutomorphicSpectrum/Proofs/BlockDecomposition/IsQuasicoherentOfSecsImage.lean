module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeIffAffineSectionsStatement
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
import Mathlib.Tactic.Lemma
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

lemma secs_mk {X : Scheme.{0}} {E F : X.Modules} (i : F ⟶ E) [Mono i] (V : X.Opens) :
    secs (Subobject.mk i) V = Set.range (i.app V) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    refine ⟨(Subobject.underlyingIso i).hom.app V x, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      Subobject.underlyingIso_hom_comp_eq_mk]
  · rintro _ ⟨x, rfl⟩
    refine ⟨(Subobject.underlyingIso i).inv.app V x, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      Subobject.underlyingIso_arrow]

lemma restrict_map_app {X : Scheme.{0}} (O : X.Opens) {Q P : X.Modules} (a : Q ⟶ P)
    (W : (O : Scheme.{0}).Opens) (y : Γ(Q.restrict O.ι, W)) :
    ((Scheme.Modules.restrictFunctor O.ι).map a).app W y =
      (P.restrictAppIso O.ι W).inv (a.app (O.ι ''ᵁ W) ((Q.restrictAppIso O.ι W).hom y)) :=
  rfl

theorem isQuasicoherent_of_secs_image {X : Scheme.{0}} (O : X.Opens) {P : X.Modules}
    {E : (O : Scheme.{0}).Modules} (hP : P.IsQuasicoherent) (hE : E.IsQuasicoherent)
    (f : P.restrict O.ι ⟶ E) (Bb : Subobject P) (hBb : (Bb : X.Modules).IsQuasicoherent)
    (B : Subobject E)
    (hB : ∀ (W : (O : Scheme.{0}).Opens), IsAffineOpen W → secs B W =
      (fun x => f.app W ((P.restrictAppIso O.ι W).inv x)) '' secs Bb (O.ι ''ᵁ W)) :
    (B : (O : Scheme.{0}).Modules).IsQuasicoherent := by
  let g : (Bb : X.Modules).restrict O.ι ⟶ E := (Scheme.Modules.restrictFunctor O.ι).map Bb.arrow ≫ f
  have hBr : ((Bb : X.Modules).restrict O.ι).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor O.ι _
  have hs : ∀ U : (O : Scheme.{0}).affineOpens,
      secs B (U : (O : Scheme.{0}).Opens) =
        secs (Subobject.mk (kernel.ι (cokernel.π g))) (U : (O : Scheme.{0}).Opens) := by
    intro U
    rw [secs_mk, range_kernel_ι_cokernel_π_app g U.2, hB _ U.2]
    ext m
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      refine ⟨((Bb : X.Modules).restrictAppIso O.ι (U : (O : Scheme.{0}).Opens)).inv y, ?_⟩
      rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, restrict_map_app, Iso.inv_hom_id_apply]
    · rintro ⟨y, rfl⟩
      refine ⟨_, ⟨((Bb : X.Modules).restrictAppIso O.ι (U : (O : Scheme.{0}).Opens)).hom y, rfl⟩, ?_⟩
      rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, restrict_map_app]
  have hEq : B = Subobject.mk (kernel.ι (cokernel.π g)) :=
    le_antisymm ((GlobalTheory.T.subobject_le_iff_affine_sections _ _).2 fun U => (hs U).subset)
      ((GlobalTheory.T.subobject_le_iff_affine_sections _ _).2 fun U => (hs U).symm.subset)
  have hK : (kernel (cokernel.π g)).IsQuasicoherent := inferInstance
  rw [hEq]
  exact GlobalTheory.QCoh.isQuasicoherent_of_iso (Subobject.underlyingIso (kernel.ι (cokernel.π g))).symm

end GlobalTheory.CompanionTheory.GE.PSupp
