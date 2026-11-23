module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.QuotMk
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GlobalTheory.DiscSpec
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

namespace UpperTheory.V.KernelIndexFullLattice

theorem cmpEquiv_holds : CmpEquiv := by
  intro E _ _ _ a μ _ _ μ₁ _ hp g v
  have hquot (q : Quot (latticeGL E a)) :
      quotMap E a (rmul (latticeGL E a) g q) =
        RightCosetSpace.rightMul (Γ1 E a) (retractOne g) (quotMap E a q) := by
    refine Quotient.inductionOn q fun x => ?_
    simp only [rmul_mk, quotMk_holds E a, RightCosetSpace.rightMul_mk, retractOne_mul]
  have hcmp (w : CuspL2 μ₁) :
      (cmp hp w : Quot (latticeGL E a) → ℂ) =ᵐ[quotMeasure (latticeGL E a) μ]
        (toLp μ₁ w : RightCosetSpace (Γ1 E a) → ℂ) ∘ quotMap E a :=
    Lp.coeFn_compMeasurePreserving (toLp μ₁ w) hp
  have hpres := measurePreserving_rmul (Γ := latticeGL E a) (μ := μ) g
  have htranslated := hpres.quasiMeasurePreserving.ae (hcmp v)
  have hrep :
      (toLp μ₁ (cuspRepT μ₁ (retractOne g) v) : RightCosetSpace (Γ1 E a) → ℂ)
        =ᵐ[RightCosetSpace.quotientMeasure (Γ1 E a) μ₁] fun x =>
          (toLp μ₁ v : RightCosetSpace (Γ1 E a) → ℂ)
            (RightCosetSpace.rightMul (Γ1 E a) (retractOne g) x) := by
    rw [toLp_cuspRepT]
    exact RightCosetSpace.coeFn_rightTranslate _ μ₁ (retractOne g) (toLp μ₁ v)
  apply Lp.ext
  filter_upwards [coeFn_R g (cmp hp v), htranslated, hcmp (cuspRepT μ₁ (retractOne g) v),
    hp.quasiMeasurePreserving.ae hrep] with q hR hleft hright hrepq
  simp only [Function.comp_apply] at hleft hright
  rw [hR, hleft, hright, hrepq, hquot]

end UpperTheory.V.KernelIndexFullLattice
