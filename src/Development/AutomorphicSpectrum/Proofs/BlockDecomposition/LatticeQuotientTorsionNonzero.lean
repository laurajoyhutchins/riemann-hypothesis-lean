module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

theorem exists_ne_zero_smul_mem_of_mem_span {K : Type} [Field K] [NumberField K] {m : ℕ}
    (L : Submodule (𝓞 K) (Fin m → K)) {v : Fin m → K}
    (hv : v ∈ Submodule.span K (L : Set (Fin m → K))) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ a • v ∈ L := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have e : (a * b) • (x + y) = b • (a • x) + a • (b • y) := by
      rw [smul_add, mul_smul, mul_comm, mul_smul]
      rw [smul_comm a b x, smul_comm b a y]
    rw [e]
    exact L.add_mem (L.smul_mem _ hax) (L.smul_mem _ hby)
  | smul k x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) k
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hdK : algebraMap (𝓞 K) K d ≠ 0 := by
      simpa using hd0
    refine ⟨d * a, mul_ne_zero hd0 ha, ?_⟩
    have e : (d * a) • ((algebraMap (𝓞 K) K n / algebraMap (𝓞 K) K d) • x) = n • (a • x) := by
      ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      simp only [Algebra.smul_def, map_mul]
      field_simp
    rw [e]
    exact L.smul_mem _ hax

theorem torsionOf_quot_lat_ne_bot : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ)
    (L : Submodule (𝓞 K) (Fin m → K)), IsLat L →
    ∀ x : (Fin m → K) ⧸ L, Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x ≠ ⊥ := by
  intro K _ _ m L hL x h
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective L x
  obtain ⟨a, ha, hav⟩ := exists_ne_zero_smul_mem_of_mem_span L
    (show v ∈ Submodule.span K (L : Set (Fin m → K)) by rw [hL.2]; trivial)
  have hmem : a ∈ Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) (Submodule.Quotient.mk v) := by
    rw [Ideal.mem_torsionOf_iff, ← Submodule.Quotient.mk_smul]
    exact (Submodule.Quotient.mk_eq_zero L).2 hav
  rw [h] at hmem
  exact ha ((Submodule.mem_bot _).1 hmem)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
