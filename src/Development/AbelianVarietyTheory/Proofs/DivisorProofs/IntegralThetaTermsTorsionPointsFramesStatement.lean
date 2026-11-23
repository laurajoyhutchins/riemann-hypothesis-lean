module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralThetaTermsTorsionPointsFrames
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT

theorem _root_.GlobalTheory.T.integral_thetaTerms_torsionPoints_frames : ∀ (m : ℕ), Odd m → 3 ≤ m → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ k : ℕ, k ≠ 0 → IsUnit (k : V₁)) → ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D (m ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))), (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ', IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' → ThetaOne.OneBasisAt D f θ') → ∀ (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∃ (b : C → (𝟙_ (Over (Sp V₁)) ⟶ D.P.A)) (t : ∀ c, LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, (b c).left] (DegPre.lineε 1))) (s₀ : V₁), (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp V₁) (p : Over.mk x ⟶ D.P.A), p ^ (m ^ 2) = 1 → ∃ c, p = toUnit _ ≫ b c) ∧ (∀ c, (t c).IsGen) ∧ (∀ c (κ : LB.Gen (kapLB D (𝟙 D.P.A ^ (m ^ 2)) ((m ^ 2) ^ 2) 1)), Normd κ → ∀ (Z : Scheme) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J → val (t c) r z J ^ ((m ^ 2) ^ 2) * val κ (r ≫ (b c).left) z J = 1) ∧ (∀ c (Z : Scheme) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J → sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (b c).left) z J * (val (t c) r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom (s₀ * u 0 c)) * (val ρ₀ r z J).val) := by
  first | exact @GlobalTheory.Poinc.Sep.FrameInt.integral_terms | exact GlobalTheory.Poinc.Sep.FrameInt.integral_terms | (intros; apply GlobalTheory.Poinc.Sep.FrameInt.integral_terms <;> assumption)
