import Formalism.HarderNarasimhan.HarderNarasimhanProofs.IntegratedRankLossSigmaBridge

/-!
# Transferring the original projection-rank estimate to integrated slope loss

This module assembles the precise numerical claims used locally by
\`theoremFSharp_of\`: a field-degree-normalized input filtration count,
a geometric placement rank estimate, monotonicity of the image submodule,
and the target filtration rank count.

The nonlinear geometric placement theorem itself remains imported only
through a separately checked source wrapper. These assumptions must
still be established from actual lattice maps before this is a proof
of a strengthened \`TheoremFSharp\`.
-/

namespace Formalism.HN

open Finset

/-- Algebraic transport from the original field-rank placement inequality
to an upper bound for the count of low target slopes. -/
theorem projectedTargetCountBound
    (d K L placed step loss δ low targetSize : ℝ)
    (hd : 0 ≤ d) (hloss : 0 ≤ loss) (hδ : δ < 1)
    (hcard : (1 - δ) * L ≤ K)
    (hplace : K - placed ≤ loss * L)
    (hcontain : placed ≤ step)
    (hcount : low = d * (K - step))
    (htotal : targetSize = d * K) :
    low ≤ ((1 - δ)⁻¹ * loss) * targetSize := by
  have hδ' : 0 < 1 - δ := by linarith
  have hL : L ≤ (1 - δ)⁻¹ * K := by
    rw [le_inv_mul_iff₀ hδ']
    exact hcard
  have hAL : loss * L ≤ loss * ((1 - δ)⁻¹ * K) :=
    mul_le_mul_of_nonneg_left hL hloss
  have hbound : K - step ≤ ((1 - δ)⁻¹ * loss) * K := by
    nlinarith [hAL, hplace, hcontain]
  calc
    low = d * (K - step) := hcount
    _ ≤ d * (((1 - δ)⁻¹ * loss) * K) :=
      mul_le_mul_of_nonneg_left hbound hd
    _ = ((1 - δ)⁻¹ * loss) * (d * K) := by ring
    _ = ((1 - δ)⁻¹ * loss) * targetSize := by rw [htotal]

/-- Source-shaped integrated geometric rank-loss implication.

The numerical hypotheses have the same roles as the original source's
\`hrkN\`, \`hfilt\`, \`hplace\`, \`hrkM\`, \`hrkSt\`, and \`hcard\`.
In particular all thresholds use one family \`a\` of input slopes.

The local geometric proof still has to discharge \`hplace\` using
\`thmF_place_exact_corank\`; this theorem does not assume it for free
when claiming to prove the original RH result. -/
theorem geometricSigmaSlopeBound
    {I : Type*} [Fintype I]
    (m n : I → ℕ) (d : ℕ) (a : ∀ i, Fin (n i) → ℝ)
    (M : ℕ) (b : Fin M → ℝ)
    (rk : ℝ → I → ℝ) (placed step : ℝ → ℝ)
    (K L s u H δ A : ℝ)
    (hd : 0 < d) (hm : 0 < ∑ i, m i) (hM : 0 < M)
    (hu : 0 ≤ u) (hH : 0 ≤ H) (hpos : 0 < u + H)
    (hδ : δ < 1) (hA : 0 ≤ A)
    (hrank : ∀ i, n i = d * m i)
    (hmean : (∑ i, (n i : ℝ)) * s ≤ ∑ i, ∑ j, a i j)
    (hupper : ∀ i j, a i j ≤ s + u)
    (hlower : ∀ j, s - H ≤ b j)
    (hfilt : ∀ t i,
      ((Finset.univ.filter (fun j : Fin (n i) => a i j < s - t)).card : ℝ) =
        (d : ℝ) * ((m i : ℝ) - rk t i))
    (htargetTotal : (M : ℝ) = (d : ℝ) * K)
    (htargetCount : ∀ t ∈ Set.Icc (0 : ℝ) H,
      ((Finset.univ.filter (fun j : Fin M => b j < s - t)).card : ℝ) =
        (d : ℝ) * (K - step t))
    (hplace : ∀ t ∈ Set.Icc (0 : ℝ) H,
      K - placed t ≤
        (A + 4 * ((∑ i, ((m i : ℝ) - rk t i)) /
          (∑ i, (m i : ℝ)))) * L)
    (hcontain : ∀ t ∈ Set.Icc (0 : ℝ) H, placed t ≤ step t)
    (hcard : (1 - δ) * L ≤ K) :
    s - (∑ j, b j) / (M : ℝ) ≤
      (1 - δ)⁻¹ * (A * H + 4 * (u * H / (u + H))) := by
  classical
  let S : Finset (Σ i, Fin (n i)) := Finset.univ
  let a' : (Σ i, Fin (n i)) → ℝ := fun ij => a ij.1 ij.2
  let R : ℝ := ∑ i, (m i : ℝ)
  let E : ℝ → ℝ := fun t => ∑ i, ((m i : ℝ) - rk t i)
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hR : 0 < R := by
    dsimp [R]
    exact_mod_cast hm
  have hS : (S.card : ℝ) = (d : ℝ) * R := by
    simpa only [S, Finset.card_univ, R] using sigmaRealRankCard m n d hrank
  have hsum : S.sum a' = ∑ i, ∑ j, a i j := by
    simpa only [S, a'] using (Fintype.sum_sigma' a)
  have htotalInput : (S.card : ℝ) = ∑ i, (n i : ℝ) := by
    simp [S, Fintype.card_sigma]
  have hmean' : (S.card : ℝ) * s ≤ S.sum a' := by
    rw [htotalInput, hsum]
    exact hmean
  have hreal : ∀ t ∈ Set.Icc (0 : ℝ) H,
      (d : ℝ) * E t =
        ((S.filter (fun ij => a' ij < s - t)).card : ℝ) := by
    intro t _
    simpa only [S, a', E] using
      (sigmaLowSlopeCorank n m a (d : ℝ) rk s hfilt t).symm
  have hE_nonneg (t : ℝ) : 0 ≤ E t := by
    have h := sigmaLowSlopeCorank n m a (d : ℝ) rk s hfilt t
    have hc : 0 ≤ ((Finset.univ.filter
        (fun ij : Σ i, Fin (n i) => a ij.1 ij.2 < s - t)).card : ℝ) :=
      Nat.cast_nonneg _
    have hmul : 0 ≤ (d : ℝ) * E t := by
      rw [← h]
      exact hc
    nlinarith
  have hgeometric : ∀ t ∈ Set.Icc (0 : ℝ) H,
      ((Finset.univ.filter (fun j : Fin M => b j < s - t)).card : ℝ) ≤
        (M : ℝ) * ((1 - δ)⁻¹ * (A + 4 * (E t / R))) := by
    intro t ht
    have hLoss : 0 ≤ A + 4 * (E t / R) := by
      have hdv : 0 ≤ E t / R := div_nonneg (hE_nonneg t) hR.le
      nlinarith
    have hh := projectedTargetCountBound (d : ℝ) K L
      (placed t) (step t) (A + 4 * (E t / R)) δ
      ((Finset.univ.filter (fun j : Fin M => b j < s - t)).card : ℝ)
      (M : ℝ) hd'.le hLoss hδ hcard
      (by simpa only [E, R] using hplace t ht)
      (hcontain t ht) (htargetCount t ht) htargetTotal
    simpa only [mul_comm] using hh
  exact realRankNormalizedCoupledSlopeBound S M a' b
    (d : ℝ) R E s u H δ A hu hH hpos hM hδ hd' hR
    hS hmean' (by intro ij _; exact hupper ij.1 ij.2)
    hlower hreal hgeometric

end Formalism.HN
