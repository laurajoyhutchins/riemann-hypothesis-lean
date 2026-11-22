import Formalism.HarderNarasimhan.HarderNarasimhanProofs.IntegratedRankLossNormalization

/-!
# The degree-normalization bridge for a dependent family of slopes

The input slopes in \`TheoremFSharp.lean\` are indexed by
\`Σ i, Fin (rk Nᵢ)\`, where the real rank is \`d\` times the coefficient-field
rank. The existing local \`hfilt\` argument identifies each low-slope count
with \`d\` times a coefficient-field corank. These lemmas sum exactly those
identities, without substituting a pointwise corank envelope.

This module is algebraic. It does not assert that the actual geometric
\`frameB_count_lt\` hypotheses are established; that source obligation remains
in \`TheoremFSharp.lean\`.
-/

namespace Formalism.HN

open Finset

/-- Rank counts for the dependent input family, with its field-degree
multiplicity preserved. -/
theorem sigmaRealRankCard {I : Type*} [Fintype I]
    (m n : I → ℕ) (d : ℕ) (hrank : ∀ i, n i = d * m i) :
    (Fintype.card (Σ i, Fin (n i)) : ℝ) =
      (d : ℝ) * ∑ i, (m i : ℝ) := by
  classical
  calc
    _ = ∑ i, (n i : ℝ) := by simp [Fintype.card_sigma]
    _ = ∑ i, (d : ℝ) * (m i : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hrank i]
      push_cast
      ring
    _ = (d : ℝ) * ∑ i, (m i : ℝ) := by rw [Finset.mul_sum]

/-- A pointwise \`hfilt\` rank/count identity at each input lattice
induces the exact *total* real-rank threshold count, for every threshold. -/
theorem sigmaLowSlopeCorank {I : Type*} [Fintype I]
    (n m : I → ℕ) (a : ∀ i, Fin (n i) → ℝ)
    (d : ℝ) (corank : ℝ → I → ℝ) (s : ℝ)
    (hfilt : ∀ t i,
      (((Finset.univ.filter (fun j : Fin (n i) => a i j < s - t)).card : ℝ)) =
        d * ((m i : ℝ) - corank t i)) :
    ∀ t,
      ((Finset.univ.filter
        (fun ij : Σ i, Fin (n i) => a ij.1 ij.2 < s - t)).card : ℝ) =
      d * ∑ i, ((m i : ℝ) - corank t i) := by
  classical
  intro t
  have hsplit :
      ((Finset.univ.filter
          (fun ij : Σ i, Fin (n i) => a ij.1 ij.2 < s - t)).card : ℝ) =
        ∑ i, (((Finset.univ.filter
          (fun j : Fin (n i) => a i j < s - t)).card : ℝ)) := by
    calc
      _ = ∑ ij : Σ i, Fin (n i),
          if a ij.1 ij.2 < s - t then (1 : ℝ) else 0 := by
            rw [Finset.sum_boole]
      _ = ∑ i, ∑ j : Fin (n i),
          if a i j < s - t then (1 : ℝ) else 0 := by
            simpa using (Fintype.sum_sigma' (fun i j => if a i j < s - t then (1 : ℝ) else 0))
      _ = ∑ i, (((Finset.univ.filter
          (fun j : Fin (n i) => a i j < s - t)).card : ℝ)) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_boole]
  calc
    _ = ∑ i, (((Finset.univ.filter
        (fun j : Fin (n i) => a i j < s - t)).card : ℝ)) := hsplit
    _ = ∑ i, d * ((m i : ℝ) - corank t i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hfilt t i
    _ = d * ∑ i, ((m i : ℝ) - corank t i) := by rw [Finset.mul_sum]

end Formalism.HN
