module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenHom
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjTwistLeray
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen

namespace GlobalTheory.CompanionTheory.GE.TwGen

theorem isQuasicoherent_imageSubobject {X : Scheme.{0}} {A B : X.Modules}
    (hA : A.IsQuasicoherent) (hB : B.IsQuasicoherent) (f : A ⟶ B) :
    (imageSubobject f : X.Modules).IsQuasicoherent := by
  haveI := hA
  haveI := hB
  have hK : (kernel (cokernel.π f)).IsQuasicoherent := inferInstance
  exact GlobalTheory.QCoh.isQuasicoherent_of_iso
    (Abelian.imageIsoImage f ≪≫ (imageSubobjectIso f).symm)

theorem isQuasicoherent_genSub : ∀ {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB)
    {P : X.Modules}, P.IsQuasicoherent → ∀ (n : ℤ) (b : Γ(GlobalTheory.twistZ P H n, ⊤)),
    (genSub hH n b : X.Modules).IsQuasicoherent := by
  intro X H hH P hP n b
  have hO : (SheafOfModules.unit X.ringCatSheaf : X.Modules).IsQuasicoherent := inferInstance
  have hS : (GlobalTheory.twistZ (SheafOfModules.unit X.ringCatSheaf) H (-n)).IsQuasicoherent :=
    GlobalTheory.Twist.isQuasicoherent_twist (F := SheafOfModules.unit X.ringCatSheaf)
      (GlobalTheory.Twist.isLB_lbZPow hH (-n))
  exact isQuasicoherent_imageSubobject hS hP _

end GlobalTheory.CompanionTheory.GE.TwGen
