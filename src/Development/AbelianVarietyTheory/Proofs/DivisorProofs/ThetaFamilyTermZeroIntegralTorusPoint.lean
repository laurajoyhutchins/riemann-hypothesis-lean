module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
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
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

noncomputable section

namespace GlobalTheory.UT.CoefZeroInt

theorem coef_zero_int : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))), (∀ (R' : Type) [CommRing R'] (f : V →+* R') θ', IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' → ThetaOne.OneBasisAt D f θ') → ∀ (th : Fam D (FractionRing V) 1), ∃ lam : FractionRing V, ∀ (g : GtPtF D (FractionRing V)) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A), g.b = toUnit _ ≫ b → ∀ (w : Frm D (FractionRing V) 1 g.b) (x : FractionRing V), IsCoef 1 g w 0 (th.s 0) x → ∀ z J, Good D.P.L z J → cst (FractionRing V) z x * (rigV D (TF (R := V) (FractionRing V)).hom z J).val = cst (FractionRing V) z lam * sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) ((toUnit (TF (R := V) (FractionRing V))).left ≫ b.left) z J * (val w (𝟙 _) z J).val := by
  intro V _ _ D θ hθ th
  obtain ⟨lam, hlam, -⟩ := existsUnique_scalar D θ hθ (FractionRing V) th
  refine ⟨lam, fun g b hb w x hx z J hJ => ?_⟩
  have h1 := hx z J hJ
  rw [pow_one] at h1
  rw [h1]
  have hs : sval (th.s 0) (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left z J =
      sval (famProj D (FractionRing V) 1 0 th) (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left z J := rfl
  have hfst : (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left ≫ famBase D (FractionRing V) = 𝟙 _ := by
    show (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left ≫ (fst (TF (R := V) (FractionRing V)) D.P.A).left = _
    rw [← Over.comp_left, lift_fst]; rfl
  have hsnd : (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left ≫ (DegPre.prB D (FractionRing V)).left =
      (toUnit (TF (R := V) (FractionRing V))).left ≫ b.left := by
    show (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left ≫ (snd (TF (R := V) (FractionRing V)) D.P.A).left = _
    rw [← Over.comp_left, lift_snd, hb, Over.comp_left]
  have hv : (Geo.Tor.val (g.s 0) (𝟙 (TF (R := V) (FractionRing V)).left) z J).val = 1 := by
    rw [val_corr hJ g.s_zero, val_one]; rfl
  have e1 := sval_smul' (π := famBase D (FractionRing V)) hJ (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left lam (termF D (FractionRing V) 1 0 θ)
  have e2 := sval_pullOver (L := D.P.L) (ε := DegPre.famε 1) (prB_hom' D (FractionRing V)) (famφ_prB D (FractionRing V) 0) θ (lift (𝟙 (TF (R := V) (FractionRing V))) g.b).left hJ
  have hc : constVal (𝟙 (TF (R := V) (FractionRing V)).left) z lam = cst (FractionRing V) z lam := rfl
  rw [hs, hlam, e1, hfst]
  erw [e2]
  rw [hsnd, hv, _root_.mul_one, hc]

end GlobalTheory.UT.CoefZeroInt
