module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.InstMeasurableSpaceMat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalRingCardinality.Params
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

noncomputable section

namespace PI.WSF

open Formalism.BasicNotions MvPolynomial MeasureTheory Measure TopologicalSpace Matrix

theorem isCompact_unitaryGroup (N : ℕ) :
    IsCompact ((Matrix.unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ))) := by
  have hK : IsCompact (Set.univ.pi fun _ : Fin N => Set.univ.pi fun _ : Fin N => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine hK.of_isClosed_subset ?_ ?_
  · have e : (Matrix.unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) =
        {A : Matrix (Fin N) (Fin N) ℂ | A * star A = 1} := by
      ext A
      exact Matrix.mem_unitaryGroup_iff
    rw [e]
    exact isClosed_eq (continuous_id.matrix_mul continuous_star) continuous_const
  · intro A hA
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
    intro i j
    exact entry_norm_bound_of_unitary hA i j

instance compactSpace_unitaryGroup (N : ℕ) : CompactSpace (Matrix.unitaryGroup (Fin N) ℂ) :=
  isCompact_iff_compactSpace.mp (isCompact_unitaryGroup N)

theorem isMulRightInvariant_of_compact {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsHaarMeasure μ] : IsMulRightInvariant μ := by
  constructor
  intro g
  haveI : (Measure.map (fun x => x * g) μ).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right μ g
  have huniv : Measure.map (fun x => x * g) μ Set.univ = μ Set.univ := by
    rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ]
  have hfin : μ Set.univ ≠ ⊤ := measure_ne_top μ _
  have hpos : μ Set.univ ≠ 0 := (isOpen_univ.measure_pos μ Set.univ_nonempty).ne'
  have hc : (Measure.map (fun x => x * g) μ).haarScalarFactor μ = 1 := by
    have h1 := Measure.measure_isHaarMeasure_eq_smul_of_isOpen (Measure.map (fun x => x * g) μ) μ
      isOpen_univ
    rw [huniv, ENNReal.smul_def] at h1
    have h2 : ((((Measure.map (fun x => x * g) μ).haarScalarFactor μ : NNReal) : ENNReal)) = 1 := by
      have h3 : (((Measure.map (fun x => x * g) μ).haarScalarFactor μ : NNReal) : ENNReal) * μ Set.univ =
          1 * μ Set.univ := by
        rw [one_mul]
        exact h1.symm
      exact (ENNReal.mul_left_inj hpos hfin).mp h3
    exact_mod_cast h2
  refine MeasureTheory.ext_of_generate_finite {s : Set G | IsOpen s}
    BorelSpace.measurable_eq isPiSystem_isOpen ?_ huniv
  intro s hs
  rw [Measure.measure_isHaarMeasure_eq_smul_of_isOpen _ μ hs, hc, one_smul]

theorem unitary_haar_measure : HaarU := by
  intro N
  haveI : CompactSpace (Matrix.unitaryGroup (Fin N) ℂ) := compactSpace_unitaryGroup N
  let μG : Measure (Matrix.unitaryGroup (Fin N) ℂ) := Measure.haarMeasure ⊤
  haveI : μG.IsMulRightInvariant := isMulRightInvariant_of_compact μG
  have hm : Measurable (Subtype.val : Matrix.unitaryGroup (Fin N) ℂ → Matrix (Fin N) (Fin N) ℂ) :=
    measurable_subtype_coe
  refine ⟨Measure.map Subtype.val μG, ?_, ?_, ?_, ?_⟩
  · constructor
    rw [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ]
    have h1 := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (Matrix.unitaryGroup (Fin N) ℂ)))
    simpa using h1
  · have hmeas : MeasurableSet {x : Matrix (Fin N) (Fin N) ℂ | x ∈ Matrix.unitaryGroup (Fin N) ℂ} :=
      (isCompact_unitaryGroup N).isClosed.measurableSet
    rw [ae_map_iff hm.aemeasurable hmeas]
    exact Filter.Eventually.of_forall fun y => y.2
  · intro u hu f hf
    have hs : AEStronglyMeasurable (fun x => f (x * u)) (Measure.map Subtype.val μG) :=
      (hf.comp (continuous_mul_const u)).aestronglyMeasurable
    rw [integral_map hm.aemeasurable hs, integral_map hm.aemeasurable hf.aestronglyMeasurable]
    have h1 := integral_mul_right_eq_self (μ := μG)
      (fun y : Matrix.unitaryGroup (Fin N) ℂ => f (y : Matrix (Fin N) (Fin N) ℂ)) ⟨u, hu⟩
    simpa using h1
  · intro u hu f hf
    have hs : AEStronglyMeasurable (fun x => f (u * x)) (Measure.map Subtype.val μG) :=
      (hf.comp (continuous_const_mul u)).aestronglyMeasurable
    rw [integral_map hm.aemeasurable hs, integral_map hm.aemeasurable hf.aestronglyMeasurable]
    have h1 := integral_mul_left_eq_self (μ := μG)
      (fun y : Matrix.unitaryGroup (Fin N) ℂ => f (y : Matrix (Fin N) (Fin N) ℂ)) ⟨u, hu⟩
    simpa using h1

end PI.WSF
