module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkOfSmoothLocal
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace MainStatements.Hodge.Pf.STALKDIM

theorem isClosed_point {k : Type} [Field k] (X : Scheme.{0}) (s : X ⟶ Sp k) (e : Sp k ⟶ X) (g : ℕ)
    (he : e ≫ s = 𝟙 _) (hs : SmoothOfRelativeDimension g s) (p : Sp k) : IsClosed ({e.base p} : Set X) := by
  have : Smooth s := hs.smooth
  have : LocallyOfFiniteType (e ≫ s) := by rw [he]; infer_instance
  have : LocallyOfFiniteType e := locallyOfFiniteType_of_comp e s
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace s
  have hp : IsClosed ({p} : Set (Sp k)) := by
    have : p = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    subst this
    exact IsLocalRing.isClosed_singleton_closedPoint k
  exact e.closePoints_subset_preimage_closedPoints hp

end MainStatements.Hodge.Pf.STALKDIM

theorem MainStatements.Hodge.Pf.stalkdim : StalkDimSt := by
  intro k _ X s e g he hs p
  have hx := MainStatements.Hodge.Pf.STALKDIM.isClosed_point X s e g he hs p
  let σ : CommRingCat.of k ⟶ X.presheaf.stalk (e.base p) := Spec.preimage (X.fromSpecStalk (e.base p) ≫ s)
  have hσ : X.fromSpecStalk (e.base p) ≫ s = Spec.map (CommRingCat.ofHom σ.hom) := by
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hloc : IsLocalHom σ.hom := by
    refine ⟨fun a ha => ?_⟩
    by_cases h0 : a = 0
    · subst h0
      simp at ha
    · exact isUnit_iff_ne_zero.mpr h0
  obtain ⟨-, -, -, hdim⟩ := GlobalTheory.StabFlat.stalk_of_smooth_local k X s g hs (e.base p) hx σ.hom hσ hloc
  rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.map_bot] at hdim
  rw [← hdim]
  exact (ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)).symm
