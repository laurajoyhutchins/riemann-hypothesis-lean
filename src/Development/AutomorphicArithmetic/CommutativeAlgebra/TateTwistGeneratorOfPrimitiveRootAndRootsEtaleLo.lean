module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.LocallyExactCech
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleLocalPrimitiveRootAndRootsOfUnity
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TateTwistSectionsLocallyGenerated
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex UpperTheory.Et

theorem UpperTheory.tateTwist_generator_of_primitiveRoot_and_roots_etaleLocal :
    ∀ (q : ℕ) [NeZero q] (i : ℤ) (U : Scheme.{0}), (∀ ζ : GlobalTheory.EtC.Prim q Γ(U, ⊤), Gen Scheme.etaleTopology q (GlobalTheory.EtC.tw q i).obj (GlobalTheory.EtC.twGen i ζ)) ∧ (UpperTheory.Et.Inv q U → LocT Scheme.etaleTopology U fun V _ => Nonempty (GlobalTheory.EtC.Prim q Γ(V, ⊤))) := by
  intro q _ i U
  obtain ⟨-, h2, h3, h4, -⟩ := UpperTheory.Cb.tateTwist_sections_locally_generated q i
  refine ⟨fun ζ => ⟨?_, ?_, ?_⟩, fun hq => (UpperTheory.Cb.etaleLocal_primitiveRoot_and_roots_of_unity q U).1 hq⟩
  · have h0 : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := ULift.ext (ZMod.natCast_self q)
    rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)) q, h0, zero_smul]
  · intro V k c hV hc
    haveI := hV
    refine h3 V (ζ.map k.appTop.hom) c ?_
    rw [← h4 V U k ζ]
    exact hc
  · intro V k y
    obtain ⟨S, hS, h⟩ := h2 V (ζ.map k.appTop.hom) y
    refine ⟨S, hS, fun W g hg => ?_⟩
    obtain ⟨c, hc⟩ := h W g hg
    refine ⟨c, hc.trans ?_⟩
    have e : GlobalTheory.EtC.twGen i ((ζ.map k.appTop.hom).map g.appTop.hom) =
        GlobalTheory.EtC.Sec.res (g ≫ k) (GlobalTheory.EtC.twGen i ζ) := by
      rw [← h4 W V g, ← h4 V U k]
      simp [GlobalTheory.EtC.Sec.res]
    rw [e]
