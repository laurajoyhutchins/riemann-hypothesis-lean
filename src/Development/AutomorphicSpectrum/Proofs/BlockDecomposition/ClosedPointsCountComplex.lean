module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyAndIsPreconnected
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodStalks

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount
namespace GlobalTheory.CompanionTheory.KoszulCount

theorem cxPts_eq_of_pt_eq {X : Scheme.{0}} {p : X ⟶ Sp ℂ} {y y' : CxPts p (RingHom.id ℂ)}
    (h : y.1 (closedPoint ℂ) = y'.1 (closedPoint ℂ)) : y = y' := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X)
    (x := y.1 (closedPoint ℂ)) (U := ⊤) trivial
  have hy : y ∈ ptsIn p (RingHom.id ℂ) U := mem_ptsIn.2 hx
  have hy' : y' ∈ ptsIn p (RingHom.id ℂ) U := mem_ptsIn.2 (h ▸ hx)
  have hv : ∀ g : Γ(X, U), ev p (RingHom.id ℂ) U g y = 0 → ev p (RingHom.id ℂ) U g y' = 0 := by
    intro g hg
    by_contra hne
    have h₁ := (mem_ptsIn_basicOpen hy' g).2 hne
    have h₂ : y ∈ ptsIn p (RingHom.id ℂ) (X.basicOpen g) := mem_ptsIn.2 (h ▸ mem_ptsIn.1 h₁)
    exact (mem_ptsIn_basicOpen hy g).1 h₂ hg
  refine Subtype.ext (GlobalTheory.Points.ext_of_valR hU hy hy' fun f => ?_)
  have e₀ : ev p (RingHom.id ℂ) U
      (f - ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U (ev p (RingHom.id ℂ) U f y)) y = 0 := by
    rw [ev_eq hy, map_sub, ← ev_eq hy, ← ev_eq hy, ev_algX hy]
    simp
  have e₁ := hv _ e₀
  rw [ev_eq hy', map_sub, ← ev_eq hy', ← ev_eq hy', ev_algX hy'] at e₁
  exact (sub_eq_zero.1 e₁).symm

theorem exists_cxPts_pt_eq {X : Scheme.{0}} (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] {x : X}
    (hx : IsClosed ({x} : Set X)) :
    ∃ y : CxPts p (RingHom.id ℂ), y.1 (closedPoint ℂ) = x := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  obtain ⟨⟨y, -, hs⟩, -⟩ :=
    GlobalTheory.SpecialisationPts.nonempty_and_isPreconnected X p inferInstance U hU x hxU
  exact ⟨y, (hs.mem_closed hx rfl : _ ∈ ({x} : Set X))⟩

theorem ncard_cxPts_over_closed : ∀ (Y : Var ℂ) (Z : Set Y.X), (∀ x ∈ Z, IsClosed ({x} : Set Y.X)) → ({y : CxPts Y.str (RingHom.id ℂ) | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z}).ncard = Z.ncard := by
  intro Y Z hZ
  have : LocallyOfFiniteType Y.str := inferInstance
  have him : (fun y : CxPts Y.str (RingHom.id ℂ) => y.1 (closedPoint ℂ)) ''
      {y : CxPts Y.str (RingHom.id ℂ) | y.1 (closedPoint ℂ) ∈ Z} = Z := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      obtain ⟨y, rfl⟩ := exists_cxPts_pt_eq Y.str (hZ x hx)
      exact ⟨y, hx, rfl⟩
  conv_rhs => rw [← him]
  exact (Set.InjOn.ncard_image fun _ _ _ _ h => cxPts_eq_of_pt_eq h).symm

end GlobalTheory.CompanionTheory.KoszulCount
