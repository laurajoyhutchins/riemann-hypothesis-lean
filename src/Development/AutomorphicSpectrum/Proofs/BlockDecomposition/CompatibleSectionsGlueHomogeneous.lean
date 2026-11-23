module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VanIdealHomog
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProjectiveCharts
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

@[expose] public section

noncomputable section

open MvPolynomial GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.SerreVan

variable {B : Type} [CommRing B] {M : ℕ}



def V0 (W : Finset (Fin M)) (P Q : Ideal (MvPolynomial (Fin M) B)) (n₀ : ℕ) : Prop :=
  ∀ n, n₀ ≤ n → ∀ f ∈ P, f.IsHomogeneous n → (∀ i ∈ W, ∃ m : ℕ, X i ^ m * f ∈ Q) → f ∈ Q

def V1 (W : Finset (Fin M)) (P Q : Ideal (MvPolynomial (Fin M) B)) (n₀ : ℕ) : Prop :=
  ∀ n, n₀ ≤ n → ∀ (k : ℕ) (f : Fin M → MvPolynomial (Fin M) B),
    (∀ i ∈ W, f i ∈ P ∧ (f i).IsHomogeneous (n + k)) →
    (∀ i ∈ W, ∀ j ∈ W, ∃ m : ℕ, (X i * X j) ^ m * (X j ^ k * f i - X i ^ k * f j) ∈ Q) →
    ∃ g ∈ P, g.IsHomogeneous n ∧ ∀ i ∈ W, ∃ m : ℕ, X i ^ m * (X i ^ k * g - f i) ∈ Q

section Extension

variable {W : Finset (Fin M)} {P P' Q : Ideal (MvPolynomial (Fin M) B)} {n₀ : ℕ}

end Extension

section Steps

variable {W : Finset (Fin M)} {P P' Q : Ideal (MvPolynomial (Fin M) B)} {n₀ : ℕ}

end Steps

section Base

variable {P Q : Ideal (MvPolynomial (Fin M) B)}

end Base

section Main

variable {P Q : Ideal (MvPolynomial (Fin M) B)}

theorem charts [IsNoetherianRing B] (W : Finset (Fin M)) :
    ∀ P Q : Ideal (MvPolynomial (Fin M) B), HomogIdeal P → HomogIdeal Q → Q ≤ P →
      (∀ j, j ∉ W → ∃ k : ℕ, ∀ f ∈ P, X j ^ k * f ∈ Q) →
      ∃ n₀, V0 W P Q n₀ ∧ V1 W P Q n₀ :=
  _root_.UpperTheory.Reformulated.B.ProjectiveCharts.charts W

theorem serre_vanishing : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (N : ℕ)
    (P : Ideal (MvPolynomial (Fin (N + 1)) B)), HomogIdeal P →
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (k : ℕ) (f : Fin (N + 1) → MvPolynomial (Fin (N + 1)) B),
      (∀ i, (f i).IsHomogeneous (n + k)) →
      (∀ i j, ∃ m : ℕ, (X i * X j) ^ m * (X j ^ k * f i - X i ^ k * f j) ∈ P) →
      ∃ g : MvPolynomial (Fin (N + 1)) B, g.IsHomogeneous n ∧
        ∀ i, ∃ m : ℕ, X i ^ m * (X i ^ k * g - f i) ∈ P := by
  intro B _ _ N P hP
  obtain ⟨n₀, -, h⟩ := charts (B := B) (M := N + 1) Finset.univ ⊤ P (fun _ _ _ => trivial) hP
    le_top (fun j hj => absurd (Finset.mem_univ j) hj)
  refine ⟨n₀, fun n hn k f hf hc => ?_⟩
  obtain ⟨g, -, hgh, hg⟩ := h n hn k f (fun i _ => ⟨trivial, hf i⟩)
    (fun i _ j _ => hc i j)
  exact ⟨g, hgh, fun i => hg i (Finset.mem_univ i)⟩

end Main

end GlobalTheory.CompanionTheory.GE.SerreVan
