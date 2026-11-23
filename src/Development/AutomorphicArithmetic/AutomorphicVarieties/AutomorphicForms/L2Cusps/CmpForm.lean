module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.QuotMk
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

open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped GlobalTheory.CuspRep.CuspidalL2GL

namespace UpperTheory.V.KernelIndexFullLattice

theorem cmpForm_holds : CmpForm := by
  intro E _ _ _ a μ _ μ₁ _ hp φ hφ
  have hRep : (toLp μ₁ (cuspVecL μ₁ φ) : RightCosetSpace (Γ1 E a) → ℂ)
      =ᵐ[RightCosetSpace.quotientMeasure (Γ1 E a) μ₁] cuspQuot φ.2.1.isLeftInvariant := by
    rw [toLp_cuspVecL]
    exact coeFn_cuspToL2 μ₁ φ
  have hQuot : (cmp hp (cuspVecL μ₁ φ) : Quot (latticeGL E a) → ℂ)
      =ᵐ[quotMeasure (latticeGL E a) μ] cuspQuot φ.2.1.isLeftInvariant ∘ quotMap E a :=
    (Lp.coeFn_compMeasurePreserving _ hp).trans (hp.quasiMeasurePreserving.ae_eq_comp hRep)
  filter_upwards [ae_quotMeasure_iff.1 hQuot] with g hg
  calc
    lift (latticeGL E a) (cmp hp (cuspVecL μ₁ φ)) g =
        cuspQuot φ.2.1.isLeftInvariant (quotMap E a (mk (latticeGL E a) g)) := hg
    _ = φ.1 g := by
      rw [quotMk_holds E a g, cuspQuot_mk, coe_retractOne, ← (Reduction.centralSection E a).map_inv]
      exact apply_mul_centralSection_of_mem hφ _ _

end UpperTheory.V.KernelIndexFullLattice
