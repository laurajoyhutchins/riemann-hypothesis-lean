module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem exists_bc_comp (R S S' C : Type) [CommRing R] [CommRing S] [CommRing S'] [Algebra R S]
    [Algebra S S'] [Algebra R S'] [IsScalarTower R S S'] [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} S) (F'' : C ⥤ CommAlgCat.{0} S')
    (m : BC F F') (n : BC F' F'') :
    ∃ l : BC F F'', ∀ T b, l.α T b = n.α T (m.α T b) := by
  obtain ⟨α, hα₁, hα₂, hα₃⟩ := m
  obtain ⟨β, hβ₁, hβ₂, hβ₃⟩ := n
  refine ⟨⟨fun T => (β T).comp (α T), ?_, ?_, ?_⟩, fun T b => rfl⟩
  · intro T T' φ b
    simp only [RingHom.comp_apply, hα₁, hβ₁]
  · intro T r b
    simp only [RingHom.comp_apply, hα₂, hβ₂, ← IsScalarTower.algebraMap_apply]
  · intro T
    obtain ⟨e₁, he₁⟩ := hα₃ T
    obtain ⟨e₂, he₂⟩ := hβ₃ T
    refine ⟨(TensorProduct.AlgebraTensorModule.cancelBaseChange R S S' S' (F.obj T)).symm.trans
      ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S' S') e₁).trans e₂), fun b => ?_⟩
    simp only [LinearEquiv.trans_apply, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply, he₁, he₂,
      RingHom.comp_apply]

end GlobalTheory.CompanionTheory.PerfVB
