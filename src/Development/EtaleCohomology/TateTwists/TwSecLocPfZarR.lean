module

public import Development.EtaleCohomology.TateTwists.TwSecLocPfR
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct GlobalTheory.EtC GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec

namespace LateralTheory.EtaleFoundations.TwSecLocPf

def AlgPow : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ζ ξ : Prim q A),
  ∃ s : Set A, Ideal.span s = ⊤ ∧ ∀ f ∈ s, ∃ (a : (ZMod q)ˣ) (n : ℕ), f ^ n * (ξ.1 - ζ.1 ^ (a : ZMod q).val) = 0

theorem ZarPow_of (hA : AlgPow) : ZarPow := by
  intro q _ V ζ ξ
  obtain ⟨s, hs, hf⟩ := hA q Γ(V, ⊤) ζ ξ
  let U : s → V.Opens := fun f => V.basicOpen f.1
  have hU : TopologicalSpace.IsOpenCover U := by
    unfold TopologicalSpace.IsOpenCover
    have h := iSup_basicOpen_of_span_eq_top ⊤ s hs
    show ⨆ f : s, V.basicOpen f.1 = ⊤
    rw [iSup_subtype]
    exact h
  let 𝒰 := V.openCoverOfIsOpenCover U hU
  refine ⟨Sieve.generate (Presieve.ofArrows 𝒰.X 𝒰.f),
    Scheme.zariskiTopology_le_etaleTopology _ (Scheme.mem_grothendieckTopology_iff.2 ⟨𝒰, Sieve.le_generate _⟩), ?_⟩
  rintro W g ⟨Y, h, _, ⟨i⟩, rfl⟩
  obtain ⟨a, n, hn⟩ := hf i.1 i.2
  refine ⟨a, ?_⟩
  have hle : (U i).ι ''ᵁ ⊤ ≤ V.basicOpen i.1 := by simp [U]
  have hu : IsUnit ((U i).ι.appTop.hom i.1) := by
    have := (V.toRingedSpace.isUnit_res_basicOpen i.1).map (V.presheaf.map (homOfLE hle).op).hom
    have e : V.presheaf.map (homOfLE (x := (U i).ι ''ᵁ ⊤) (y := ⊤) le_top).op =
        V.presheaf.map (homOfLE (V.basicOpen_le i.1)).op ≫ V.presheaf.map (homOfLE hle).op := by
      rw [← Functor.map_comp]; rfl
    rw [Scheme.Opens.ι_appTop, e]
    exact this
  have key : (U i).ι.appTop.hom ξ.1 = ((U i).ι.appTop.hom ζ.1) ^ (a : ZMod q).val := by
    have h0 : (U i).ι.appTop.hom (i.1 ^ n * (ξ.1 - ζ.1 ^ (a : ZMod q).val)) = 0 := by rw [hn, map_zero]
    rw [map_mul, map_pow, map_sub, map_pow] at h0
    exact sub_eq_zero.1 ((hu.pow n).mul_right_eq_zero.1 h0)
  have hc : ∀ x, (h ≫ (U i).ι).appTop.hom x = h.appTop.hom ((U i).ι.appTop.hom x) := fun x => by
    rfl
  show (h ≫ (U i).ι).appTop.hom ξ.1 = ((h ≫ (U i).ι).appTop.hom ζ.1) ^ _
  rw [hc, hc, key]
  exact map_pow _ _ _

theorem TwSecLoc_of_alg (hA : AlgPow) : LateralTheory.EtaleFoundations.TwLocPf.TwSecLoc := TwSecLoc_of (ZarPow_of hA)

end LateralTheory.EtaleFoundations.TwSecLocPf
