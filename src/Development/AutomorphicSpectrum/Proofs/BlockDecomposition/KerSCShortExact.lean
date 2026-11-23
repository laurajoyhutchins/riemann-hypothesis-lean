module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.HasFiniteBiproductsModules
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory.CompanionTheory.GE.KerSeq

variable {X : Scheme.{0}} {k : ℕ} {M : ℕ → X.Modules}

abbrev sumN (M : ℕ → X.Modules) (k d e : ℕ) : X.Modules := ⨁ fun _ : Fin k => M (d + e)

def sumMap (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d e : ℕ) : sumN M k d e ⟶ M (d + e + 1) :=
  biproduct.desc fun i => T i (d + e)

def diagOp (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d : ℕ) (j : Fin k) (e : ℕ) :
    sumN M k d e ⟶ sumN M k d (e + 1) :=
  biproduct.map fun _ => T j (d + e)

abbrev kerSeq (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d e : ℕ) : X.Modules := kernel (sumMap T d e)

theorem diagOp_sumMap (T : Fin k → ∀ e, M e ⟶ M (e + 1))
    (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (d : ℕ) (j : Fin k) (e : ℕ) :
    diagOp T d j e ≫ sumMap T d (e + 1) = sumMap T d e ≫ T j (d + e + 1) := by
  apply biproduct.hom_ext'
  intro i
  simp only [diagOp, sumMap, biproduct.ι_map_assoc, biproduct.ι_desc, biproduct.ι_desc_assoc]
  exact hc j i (d + e)

def kerOp (T : Fin k → ∀ e, M e ⟶ M (e + 1))
    (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (d : ℕ) (j : Fin k) (e : ℕ) :
    kerSeq T d e ⟶ kerSeq T d (e + 1) :=
  kernel.lift _ (kernel.ι _ ≫ diagOp T d j e) (by
    rw [Category.assoc, diagOp_sumMap T hc, kernel.condition_assoc, zero_comp])

@[reassoc (attr := simp)]
theorem kerOp_ι (T : Fin k → ∀ e, M e ⟶ M (e + 1))
    (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (d : ℕ) (j : Fin k) (e : ℕ) :
    kerOp T hc d j e ≫ kernel.ι _ = kernel.ι _ ≫ diagOp T d j e :=
  kernel.lift_ι _ _ _

theorem diagOp_comm (T : Fin k → ∀ e, M e ⟶ M (e + 1))
    (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (d : ℕ) (i j : Fin k) (e : ℕ) :
    diagOp T d i e ≫ diagOp T d j (e + 1) = diagOp T d j e ≫ diagOp T d i (e + 1) := by
  apply biproduct.hom_ext
  intro l
  simp only [diagOp, Category.assoc, biproduct.map_π, biproduct.map_π_assoc]
  exact biproduct.π _ l ≫= hc i j (d + e)

theorem kerOp_comm (T : Fin k → ∀ e, M e ⟶ M (e + 1))
    (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (d : ℕ) (i j : Fin k) (e : ℕ) :
    kerOp T hc d i e ≫ kerOp T hc d j (e + 1) = kerOp T hc d j e ≫ kerOp T hc d i (e + 1) := by
  rw [← cancel_mono (kernel.ι _)]
  simp only [Category.assoc, kerOp_ι, kerOp_ι_assoc]
  rw [diagOp_comm T hc]

def kerSC (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d e : ℕ) : ShortComplex X.Modules :=
  ShortComplex.mk (kernel.ι (sumMap T d e)) (sumMap T d e) (kernel.condition _)

theorem kerSC_shortExact (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d e : ℕ) [Epi (sumMap T d e)] :
    (kerSC T d e).ShortExact :=
  ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _))
    (inferInstanceAs (Mono (kernel.ι (sumMap T d e))))
    (inferInstanceAs (Epi (sumMap T d e)))

end GlobalTheory.CompanionTheory.GE.KerSeq
