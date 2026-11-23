module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory

theorem exists_short_integral_rational_basis :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ (n : ℕ) (ω : Fin n → 𝓞 E),
      (∀ j (σ : E →+* ℂ), ‖σ (ω j)‖ ≤ omStar (E := E)) ∧
      ∀ α : 𝓞 E, (α : E) ∈ Submodule.span ℚ (Set.range fun j => (ω j : E))) →
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
      ∃ ω : Fin (Module.finrank ℚ E) → 𝓞 E, LinearIndependent ℚ (fun j => (ω j : E)) ∧
        ∀ j (τ : E →+* ℂ), ‖τ (ω j : E)‖ ≤ omStar (E := E)) := by
  intro hex E _ _ _
  classical
  obtain ⟨n, ω, hωB, hsp⟩ := hex E
  have htop : Submodule.span ℚ (Set.range fun j => (ω j : E)) = ⊤ := by
    rw [eq_top_iff, ← (NumberField.integralBasis E).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [NumberField.integralBasis_apply]
    exact hsp _
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent ℚ (Set.range fun j => (ω j : E))
  have hbfin : b.Finite := hbli.setFinite
  have := hbfin.fintype
  have hcard : Fintype.card b = Module.finrank ℚ E := by
    have h := finrank_span_eq_card hbli
    rw [Subtype.range_coe, hbspan, htop, finrank_top] at h
    rw [h]
  let e : Fin (Module.finrank ℚ E) ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hmem : ∀ x : b, ∃ j, (ω j : E) = x := fun x => hbS x.2
  choose idx hidx using hmem
  refine ⟨fun i => ω (idx (e i)), ?_, fun i τ => hωB _ τ⟩
  have : (fun i => ((ω (idx (e i)) : 𝓞 E) : E)) = (fun x : b => (x : E)) ∘ e := by
    funext i; simp [hidx]
  rw [this]
  exact (linearIndependent_equiv e).mpr hbli

end GlobalTheory
