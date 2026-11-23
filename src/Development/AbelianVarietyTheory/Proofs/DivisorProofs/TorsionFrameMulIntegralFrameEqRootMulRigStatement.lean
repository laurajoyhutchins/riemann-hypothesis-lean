module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFrameMulIntegralFrameEqRootMulRig
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT

theorem _root_.GlobalTheory.T.torsionFrame_mul_integralFrame_eq_root_mul_rig : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (K : Type) [Field K] (ev : V₁ →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∀ (n : ℕ), 1 ≤ n → ∀ (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A) (τ : LB.Gen (LB.LinComb D.P.L (Y := (Over.mk (spMap ev)).left) (K := Fin 1) (fun _ => (toUnit (Over.mk (spMap ev)) ≫ b).left) (fun _ => 1))), IsTorsFrame D.P ρ₀ n (toUnit (Over.mk (spMap ev)) ≫ b) τ → ∀ (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))), t.IsGen → (∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ n) (n ^ 2) 1), Normd κ → ∀ (z : (Over.mk (spMap ev)).left) J, Good D.P.L z J → val t (Over.mk (spMap ev)).hom z J ^ (n ^ 2) * val κ ((Over.mk (spMap ev)).hom ≫ b.left) z J = 1) → ∃ ζ : K, ζ ^ (n ^ 2) = 1 ∧ ∀ (z : (Over.mk (spMap ev)).left) J, Good D.P.L z J → (val τ (𝟙 _) z J).val * (val t (Over.mk (spMap ev)).hom z J).val = gs (𝟙 (Over.mk (spMap ev)).left) z ⊤ (GlobalTheory.Ex.fnOf ζ) * (val ρ₀ (Over.mk (spMap ev)).hom z J).val := by
  first | exact @GlobalTheory.USep.FrameRoot.frame_mul_eq_root | exact GlobalTheory.USep.FrameRoot.frame_mul_eq_root | (intros; apply GlobalTheory.USep.FrameRoot.frame_mul_eq_root <;> assumption)
