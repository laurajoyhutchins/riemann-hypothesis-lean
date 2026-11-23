module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSystemPullbackStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerKillsSystemStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonemptyOpenIdealNotNilpotentStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperBirationalClosedSystemStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperPullbackSystemQuasicoherentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperPushforwardCoherentStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperSupportPullbackSystemStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PushforwardClosedSystemUnseenStatement
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.CokernelCoherent
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.PullbackCoherent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

theorem core_integral_step : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))] [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] (J : X.IdealSheafData) [IsIntegral J.subscheme] {Z : Scheme.{0}} [Z.Over (Spec (.of A))], Statement I (⊥ : Z.IdealSheafData) → ∀ (ψ : Z ⟶ J.subscheme), IsProper ψ → (ψ ≫ J.subschemeι) ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ (W : J.subscheme.Opens), (W : Set J.subscheme).Nonempty → IsIso (ψ ∣_ W) → ∀ {E : X.Modules}, IsCoherent E → ∀ {S : ℕ → Subobject E}, ClosedSys I E S → (∀ e, Killed J (S e)) → PropSupp A (S 0) → ∃ (D : Subobject E) (c : ℕ) (J' : X.IdealSheafData), (D : X.Modules).IsQuasicoherent ∧ PropSupp A D ∧ (∀ e, S (e + c) ≤ D ⊔ powSub I E (e + 1)) ∧ J < J' ∧ ∀ (n : ℕ) (U : X.affineOpens) (a : Γ(X, U)), a ∈ J'.ideal U → ∀ x ∈ secs D U, a • x ∈ secs (S n) U := by
  intro A _ _ I _ X _ _ _ _ J _ Z _ hZ ψ hψ hover W hW hiso E hE S hS hK hP
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have hcs : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))
  have hφ : IsProper (ψ ≫ J.subschemeι) := by
    haveI := hψ
    infer_instance
  have hcl := GlobalTheory.T.closed_system_pullback I (ψ ≫ J.subschemeι) hover hE hS
  have hps := GlobalTheory.T.proper_support_pullback_system I (ψ ≫ J.subschemeι) hφ hover hE hS hP
  have hEZ := isCoherent_pullback (ψ ≫ J.subschemeι) hE
  obtain ⟨B, hBq, hBP, hB⟩ := hZ _ hEZ _ hcl (fun e U a ha x => by
    have ha0 : a = 0 := by simpa using ha
    subst ha0
    exact ⟨0, by rw [map_zero, zero_smul]⟩) hps
  have := hEZ.1
  have hG : IsCoherent (cokernel B.arrow) := isCoherent_cokernel B.arrow hEZ
  have hP' := GlobalTheory.T.proper_pushforward_coherent (ψ ≫ J.subschemeι) hφ hG
  have := hP'.1
  have hE1 := hE.1
  have hDq : ((adjKer (ψ ≫ J.subschemeι) B : Subobject E) : X.Modules).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (kernelSubobjectIso (adjMap (ψ ≫ J.subschemeι) B)).symm
      (isCoherent_kernel (adjMap (ψ ≫ J.subschemeι) B) hE).1
  obtain ⟨c, hc⟩ := GlobalTheory.T.proper_pullback_system_quasicoherent I (ψ ≫ J.subschemeι) hφ hover hE hS B hBq hB
  obtain ⟨J₀, hJ₀, hJ₀J⟩ := GlobalTheory.T.nonempty_open_ideal_not_nilpotent J W hW
  obtain ⟨m, hm⟩ := GlobalTheory.T.ideal_power_kills_system hE (adjKer (ψ ≫ J.subschemeι) B) hDq S hS.qcoh J₀
    (fun V f hf x hx => GlobalTheory.T.proper_birational_closed_system I J ψ hψ hover W hiso hE hS hK B hB V f (hJ₀ V f hf) x hx)
  refine ⟨adjKer (ψ ≫ J.subschemeι) B, c, J ⊔ powIdeal J₀ m, hDq,
    GlobalTheory.T.pushforward_closed_system_auxiliary (ψ ≫ J.subschemeι) hφ hover B hBP, hc, ?_, ?_⟩
  · exact lt_of_le_of_ne le_sup_left (fun h => hJ₀J m (h ▸ le_sup_right))
  · intro n U a ha x hx
    obtain ⟨a₁, h₁, a₂, h₂, rfl⟩ := Submodule.mem_sup.1 ha
    rw [add_smul]
    obtain ⟨y, rfl⟩ := hx
    exact (secsSub (S n) U).add_mem (hK n U a₁ h₁ _) (hm n U a₂ h₂ _ ⟨y, rfl⟩)

end GlobalTheory.CompanionTheory.GE
