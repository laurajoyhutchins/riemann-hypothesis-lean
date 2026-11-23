module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.MPSmooth

def chartHom (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) : Γ(PSpace ℤ N, chart ℤ N c) →+* ℂ :=
  (MvPolynomial.eval₂Hom (Int.castRingHom ℂ) (fun j : {j // j ≠ c} => w j.1 / w c)).comp
    (chartAlgEquiv ℤ N c).symm.toRingEquiv.toRingHom

def ptP (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) : CxPts (PSpace.str ℤ N) σ₀ :=
  CxPts.ofHom (isAffineOpen_chart ℤ N c) (chartHom N c w)
    (fun a => RingHom.congr_fun (RingHom.ext_int ((chartHom N c w).comp (DVR.FlatBC.algX _ _)) σ₀) a)

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

def multiprojectivePoint (c : ∀ k, Bk n k) (z : (Σ k, Bk n k) → ℂ) : CxPts (mpStr ℤ m n) σ₀ :=
  ⟨GroundTheory.Arith.SchemeCoh.ProjSpace.lift m n (spMap σ₀)
      (fun k => (ptP (n k) (c k) (fun i => z ⟨k, i⟩)).1) (fun k => (ptP (n k) (c k) (fun i => z ⟨k, i⟩)).2),
    GroundTheory.Arith.SchemeCoh.ProjSpace.lift_mpStr _ _ _ _ _⟩

theorem map_prB_ptMP (c : ∀ k, Bk n k) (z : (Σ k, Bk n k) → ℂ) (k : Fin (m + 1)) :
    (GlobalTheory.Points.PtsOver.map (prB n k) (GroundTheory.Arith.SchemeCoh.ProjSpace.pr_toSpecBase ℤ m n k) _ (multiprojectivePoint c z)) =
      ptP (n k) (c k) (fun i => z ⟨k, i⟩) :=
  Subtype.ext (GroundTheory.Arith.SchemeCoh.ProjSpace.lift_pr _ _ _ _ _ k)

end GlobalTheory.CompanionTheory.MPSmooth
