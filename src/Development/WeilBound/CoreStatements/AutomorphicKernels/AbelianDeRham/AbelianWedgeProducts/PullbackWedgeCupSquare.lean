module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianPullbackLattices.CompositeRestrictionPullInjective
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.IsPullbackH2Structure
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

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace MainStatements.Hodge.Pf.WedgeProjections

variable {R : Type} [CommRing R]

theorem pullback_wedge_cup_square {Y Z : Over (Sp R)} (f : Y ⟶ Z)
    (eZ : ⋀[R]^2 (HO1 Z.hom) ≃ₗ[R] H2 (OAff Z.hom))
    (hZ : ∀ a b, eZ (exteriorPower.ιMulti R 2 ![a, b]) = cup (OAff Z.hom) a b)
    (eY : ⋀[R]^2 (HO1 Y.hom) ≃ₗ[R] H2 (OAff Y.hom))
    (hY : ∀ a b, eY (exteriorPower.ιMulti R 2 ![a, b]) = cup (OAff Y.hom) a b) (t : ⋀[R]^2 (HO1 Z.hom)) :
    IsPullbackH2Structure (wOver f) (eZ t) (eY (exteriorPower.map 2 (AXO.pO f) t)) := by
  unfold IsPullbackH2Structure
  have ht : t ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 2 (M := HO1 Z.hom))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    have hv : v = ![v 0, v 1] := by
      ext i
      fin_cases i <;> rfl
    have hv2 : (⇑(AXO.pO f) ∘ ![v 0, v 1]) = ![AXO.pO f (v 0), AXO.pO f (v 1)] := by
      ext i
      fin_cases i <;> rfl
    have h0 : (pairPull (wOver f)).pull1 (v 0) = (pairRes f.left Y.hom).pull1 (AXO.pO f (v 0)) :=
      (AXO.pO_spec f (v 0) _).2 rfl
    have h1 : (pairPull (wOver f)).pull1 (v 1) = (pairRes f.left Y.hom).pull1 (AXO.pO f (v 1)) :=
      (AXO.pO_spec f (v 1) _).2 rfl
    rw [hv, exteriorPower.map_apply_ιMulti, hv2, hZ, hY, CoefMap.pullCohomologyTwo_cup, CoefMap.pullCohomologyTwo_cup, h0, h1]
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  | smul a x _ hx =>
    simp only [map_smul, map_smulₛₗ, RingHom.id_apply]
    rw [hx]

end MainStatements.Hodge.Pf.WedgeProjections
