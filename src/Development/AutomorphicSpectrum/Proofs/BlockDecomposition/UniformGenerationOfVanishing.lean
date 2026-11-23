module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelOperatorsSpanEventuallyStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelSequenceCoherentStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OperatorSequenceSumEpiStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedVanishingSectionsSpanStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformSpanEventuallyStatement
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerSCShortExact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

theorem uniformGen_of_gradedNoeth : GradedNoeth → UniformVanishing → UniformGen := by
  intro hN hV A _ _ X _ _ H hH k M T d hM
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have hcs : CompactSpace X := hH.compactSpace
  have hcoh := GlobalTheory.T.kernel_sequence_coherent hM
  obtain ⟨d', hd'⟩ := GlobalTheory.T.uniform_span_eventually (KerSeq.kerOp T hM.comm d) (fun e => (hcoh e).1)
    (GlobalTheory.T.kernel_operators_span_eventually hN hM)
  have hK : OpSeq k (KerSeq.kerSeq T d) (KerSeq.kerOp T hM.comm d) d' :=
    ⟨hcoh, KerSeq.kerOp_comm T hM.comm d, hd'⟩
  obtain ⟨n₀, hn₀⟩ := hV (A := A) H hH k _ _ d' hK
  refine ⟨n₀, fun n hn e he => ?_⟩
  obtain ⟨e₀, rfl⟩ := Nat.exists_eq_add_of_le he
  haveI := GlobalTheory.T.operator_sequence_sum_epi hM e₀
  exact GlobalTheory.T.twisted_vanishing_sections_span (GlobalTheory.lbZPow H n) (GlobalTheory.Twist.isLB_lbZPow hH.isLB n) (fun i => T i (d + e₀))
    (kernel.ι _) (kernel.condition _) (KerSeq.kerSC_shortExact T d e₀) (hn₀ n hn e₀ 1 one_pos)

end GlobalTheory.CompanionTheory.GE
