module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinCol
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph

@[expose] public section

open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.FSCrofton

theorem measurePreserving_funUnique_symm {U : Type} [inst : Fintype U] [Unique U] :
    MeasurePreserving (MeasurableEquiv.funUnique U ℂ).symm (volume : Measure ℂ)
      (Measure.pi fun _ : U => (volume : Measure ℂ)) := by
  obtain rfl : inst = Unique.fintype := Subsingleton.elim _ _
  exact (measurePreserving_funUnique (volume : Measure ℂ) U).symm

theorem measurePreserving_joinEntry {α : Type} [Fintype α] [DecidableEq α] (j₀ : α) :
    MeasurePreserving
      (fun p : ℂ × ({j : α // j ≠ j₀} → ℂ) =>
        (fun j => if h : j = j₀ then p.1 else p.2 ⟨j, h⟩ : α → ℂ))
      ((volume : Measure ℂ).prod (Measure.pi fun _ : {j : α // j ≠ j₀} => (volume : Measure ℂ)))
      (Measure.pi fun _ : α => (volume : Measure ℂ)) := by
  haveI : Unique {j : α // ¬ j ≠ j₀} :=
    { default := ⟨j₀, by simp⟩
      uniq := fun x => Subtype.ext (by simpa using x.2) }
  have h1 := (measurePreserving_piEquivPiSubtypeProd (fun _ : α => (volume : Measure ℂ))
    (fun j => j ≠ j₀)).symm
  have h2 : MeasurePreserving (MeasurableEquiv.funUnique {j : α // ¬ j ≠ j₀} ℂ).symm
      (volume : Measure ℂ) (Measure.pi fun _ : {j : α // ¬ j ≠ j₀} => (volume : Measure ℂ)) :=
    measurePreserving_funUnique_symm
  have h3 := (MeasurePreserving.id
    (Measure.pi fun _ : {j : α // j ≠ j₀} => (volume : Measure ℂ))).prod h2
  have h4 : MeasurePreserving (Prod.swap : ℂ × ({j : α // j ≠ j₀} → ℂ) → _)
      ((volume : Measure ℂ).prod (Measure.pi fun _ : {j : α // j ≠ j₀} => (volume : Measure ℂ)))
      ((Measure.pi fun _ : {j : α // j ≠ j₀} => (volume : Measure ℂ)).prod (volume : Measure ℂ)) :=
    Measure.measurePreserving_swap
  have h5 := h1.comp (h3.comp h4)
  convert h5 using 1
  funext p j
  by_cases h : j = j₀
  · subst h
    simp [MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd]
  · simp [MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, h]

theorem measurePreserving_joinCol (d : ℕ) {α : Type} [Fintype α] [DecidableEq α] (j₀ : α) :
    MeasurePreserving
      (fun p : (Fin d → ℂ) × (Fin d → {j : α // j ≠ j₀} → ℂ) => joinCol j₀ p.1 p.2)
      volume volume := by
  have h1 := (volume_measurePreserving_arrowProdEquivProdArrow ℂ ({j : α // j ≠ j₀} → ℂ) (Fin d)).symm
  have h2 := measurePreserving_pi (fun _ : Fin d => (volume : Measure (ℂ × ({j : α // j ≠ j₀} → ℂ))))
    (fun _ : Fin d => (volume : Measure (α → ℂ))) (fun _ => measurePreserving_joinEntry j₀)
  exact h2.comp h1

theorem lintegral_joinCol : ∀ (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α) (Φ : (Fin d → α → ℂ) → ℝ≥0∞), Measurable Φ → ∫⁻ C : Fin d → α → ℂ, Φ C = ∫⁻ C' : Fin d → {j : α // j ≠ j₀} → ℂ, ∫⁻ c : Fin d → ℂ, Φ (joinCol j₀ c C') := by
  intro d α _ _ j₀ Φ hΦ
  have hT := measurePreserving_joinCol d j₀
  rw [← hT.lintegral_comp hΦ]
  exact lintegral_prod_symm _ (hΦ.comp hT.measurable).aemeasurable

end GlobalTheory.CompanionTheory.FSCrofton
