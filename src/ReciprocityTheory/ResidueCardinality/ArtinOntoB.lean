module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.Automorphisms.InstMainA

@[expose] public section

noncomputable section

namespace ReciprocityTheory.Bridge.ResidueFieldCardinality

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {F : Type} [Field F] [NumberField F]



theorem card_residue (v : HeightOneSpectrum (𝓞 F)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = Nat.card (𝓞 F ⧸ v.asIdeal) := by
  classical
  have hcoeO : ∀ r : 𝓞 F, ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) r :
      v.adicCompletionIntegers F) : v.adicCompletion F) = algebraMap (𝓞 F) (v.adicCompletion F) r := by
    intro r
    rfl
  have hvR : ∀ r : 𝓞 F, Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) = v.intValuation r := by
    intro r
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]
    first
    | (rw [v.valuedAdicCompletion_eq_valuation']; exact v.valuation_of_algebraMap r)
    | (rw [v.valuedAdicCompletion_eq_valuation]; exact v.valuation_of_algebraMap r)
    | (erw [v.valuedAdicCompletion_eq_valuation']; exact v.valuation_of_algebraMap r)
    | simp [v.valuedAdicCompletion_eq_valuation', v.valuation_of_algebraMap]
    | simp [v.valuedAdicCompletion_eq_valuation, v.valuation_of_algebraMap]
  have hmem : ∀ r : 𝓞 F, r ∈ v.asIdeal ↔ v.intValuation r < 1 := by
    intro r
    exact (v.intValuation_lt_one_iff_mem r).symm
  have hpow : ∀ (r : 𝓞 F) (m : ℕ), r ∈ v.asIdeal ^ m ↔
      v.intValuation r ≤ WithZero.exp (-(m : ℤ)) := by
    intro r m
    exact (v.intValuation_le_pow_iff_mem r m).symm
  have hvp : Prime v.asIdeal := v.prime
  have hcl : ∀ a b : 𝓞 F, b ≠ 0 → v.intValuation a ≤ v.intValuation b →
      ∃ c : 𝓞 F, v.intValuation (a - b * c) < v.intValuation b := by
    intro a b hb hab
    obtain ⟨n, hn⟩ : ∃ n : ℕ, v.intValuation b = WithZero.exp (-(n : ℤ)) :=
      ⟨_, v.intValuation_if_neg hb⟩
    have hbn1 : b ∉ v.asIdeal ^ (n + 1) := by
      intro h
      have h' := (hpow b (n + 1)).mp h
      rw [hn, WithZero.exp_le_exp] at h'
      push_cast at h'
      omega
    have han : a ∈ v.asIdeal ^ n := (hpow a n).mpr (hab.trans (le_of_eq hn))
    have hJ : (Ideal.span {b} ⊔ v.asIdeal ^ (n + 1)) ∣ v.asIdeal ^ (n + 1) :=
      Ideal.dvd_iff_le.mpr le_sup_right
    obtain ⟨i, hi, hJi⟩ := (dvd_prime_pow hvp (n + 1)).mp hJ
    have hJeq : Ideal.span {b} ⊔ v.asIdeal ^ (n + 1) = v.asIdeal ^ i := associated_iff_eq.mp hJi
    have hin : i ≤ n := by
      by_contra h
      have hi' : i = n + 1 := by omega
      apply hbn1
      rw [← hi', ← hJeq]
      exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self b)
    have haJ : a ∈ Ideal.span {b} ⊔ v.asIdeal ^ (n + 1) := by
      rw [hJeq]
      exact Ideal.pow_le_pow_right hin han
    obtain ⟨y, hy, e, he, hye⟩ := Submodule.mem_sup.mp haJ
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hy
    refine ⟨c, ?_⟩
    have hae : a - b * c = e := by rw [← hye]; ring
    rw [hae, hn]
    have h' := (hpow e (n + 1)).mp he
    refine lt_of_le_of_lt h' ?_
    rw [WithZero.exp_lt_exp]
    push_cast
    omega
  have hdense : DenseRange (algebraMap F (v.adicCompletion F)) := denseRange_algebraMap F v
  have happrox : ∀ z : v.adicCompletion F, ∃ k : F,
      Valued.v (z - algebraMap F (v.adicCompletion F) k) < 1 := by
    intro z
    have hU : {w : v.adicCompletion F | Valued.v (w - z) < 1} ∈ nhds z := by
      rw [Valued.mem_nhds]
      exact ⟨1, fun w hw => by simpa using hw⟩
    obtain ⟨w, hw, k, rfl⟩ := mem_closure_iff_nhds.mp (hdense z) _ hU
    refine ⟨k, ?_⟩
    rw [Valuation.map_sub_swap]
    exact hw
  have hsurj : Function.Surjective ((IsLocalRing.residue (v.adicCompletionIntegers F)).comp
      (algebraMap (𝓞 F) (v.adicCompletionIntegers F))) := by
    intro y
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨k, hk⟩ := happrox (z : v.adicCompletion F)
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 F) k
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbF : algebraMap (𝓞 F) F b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hb0
    have hz : Valued.v (z : v.adicCompletion F) ≤ 1 := z.2
    have hk1 : Valued.v (algebraMap F (v.adicCompletion F) k) ≤ 1 := by
      have hsplit : algebraMap F (v.adicCompletion F) k =
          (z : v.adicCompletion F) - ((z : v.adicCompletion F) - algebraMap F (v.adicCompletion F) k) := by
        ring
      rw [hsplit]
      exact Valuation.map_sub_le _ hz hk.le
    have hkb : algebraMap F (v.adicCompletion F) k * algebraMap (𝓞 F) (v.adicCompletion F) b =
        algebraMap (𝓞 F) (v.adicCompletion F) a := by
      rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F) b,
        IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F) a, ← map_mul, ← hab,
        div_mul_cancel₀ _ hbF]
    have hvab : v.intValuation a ≤ v.intValuation b := by
      rw [← hvR, ← hvR, ← hkb, map_mul]
      calc _ ≤ 1 * Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) b) := by gcongr
        _ = _ := one_mul _
    obtain ⟨c, hc⟩ := hcl a b hb0 hvab
    have hkc : Valued.v (algebraMap F (v.adicCompletion F) k -
        algebraMap (𝓞 F) (v.adicCompletion F) c) < 1 := by
      have h1 : (algebraMap F (v.adicCompletion F) k - algebraMap (𝓞 F) (v.adicCompletion F) c) *
          algebraMap (𝓞 F) (v.adicCompletion F) b = algebraMap (𝓞 F) (v.adicCompletion F) (a - b * c) := by
        rw [sub_mul, hkb, map_sub, map_mul]
        ring
      have h2 := congrArg Valued.v h1
      rw [map_mul, hvR b, hvR (a - b * c)] at h2
      by_contra hcon
      push_neg at hcon
      have hle : v.intValuation b ≤ v.intValuation (a - b * c) := by
        calc v.intValuation b = 1 * v.intValuation b := (one_mul _).symm
          _ ≤ _ := by gcongr
          _ = _ := h2
      exact absurd hc (not_lt.mpr hle)
    refine ⟨c, ?_⟩
    rw [RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      ReciprocityTheory.Aut.mem_maxIdeal_iff]
    have hco : ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) c - z : v.adicCompletionIntegers F) :
        v.adicCompletion F) = algebraMap (𝓞 F) (v.adicCompletion F) c - (z : v.adicCompletion F) := by
      rw [← hcoeO c]
      rfl
    rw [hco]
    have hsum : algebraMap (𝓞 F) (v.adicCompletion F) c - (z : v.adicCompletion F) =
        -(algebraMap F (v.adicCompletion F) k - algebraMap (𝓞 F) (v.adicCompletion F) c) +
          -((z : v.adicCompletion F) - algebraMap F (v.adicCompletion F) k) := by
      ring
    rw [hsum]
    apply Valuation.map_add_lt
    · rw [Valuation.map_neg]
      exact hkc
    · rw [Valuation.map_neg]
      exact hk
  have hker : RingHom.ker ((IsLocalRing.residue (v.adicCompletionIntegers F)).comp
      (algebraMap (𝓞 F) (v.adicCompletionIntegers F))) = v.asIdeal := by
    ext r
    rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff,
      ReciprocityTheory.Aut.mem_maxIdeal_iff, hcoeO, hvR, hmem]
  exact (Nat.card_congr ((Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective hsurj)).toEquiv).symm

end ReciprocityTheory.Bridge.ResidueFieldCardinality
