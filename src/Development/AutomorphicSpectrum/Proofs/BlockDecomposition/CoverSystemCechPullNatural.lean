module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.PullCochMemCoboundaries
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechConnectingPullNaturalStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechH0PullCompatStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechSheafCohomologyPullCompatStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveResolutionLiftPushforward
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
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.CechLerayPull

theorem cechHEquiv_pull {X Y : TopCat.{0}} (f : X ⟶ Y) {BY : Opens Y → Prop}
    {GoodY : ∀ {κ : Type}, Opens Y → (κ → Opens Y) → Prop} {BX : Opens X → Prop}
    {GoodX : ∀ {κ : Type}, Opens X → (κ → Opens X) → Prop} (hCY : IsCoverSystem BY GoodY) (hCX : IsCoverSystem BX GoodX)
    {κ ι : Type} (V : κ → Opens Y) (hV : iSup V = ⊤) (hVB : ∀ {n : ℕ} (i : Fin (n + 1) → κ), BY (inter V i))
    (U : ι → Opens X) (hU : iSup U = ⊤) (hUB : ∀ {n : ℕ} (i : Fin (n + 1) → ι), BX (inter U i)) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) : ∀ (n : ℕ) {G : AbSheaf Y} {G' : AbSheaf X}
    (hG : GoodAcyclic BY GoodY G) (hG' : GoodAcyclic BX GoodX G') (φ : G ⟶ (push f).obj G') (x : GroundTheory.Arith.SchemeCoh.cechH G.obj V n),
    (cechHEquiv hCX U hU hUB n G' hG' : GroundTheory.Arith.SchemeCoh.cechH G'.obj U n ≃+ Sheaf.H.{0} G' n) (cechPullH f φ.hom V U τ hτ n x) =
      hPull f φ n ((cechHEquiv hCY V hV hVB n G hG : GroundTheory.Arith.SchemeCoh.cechH G.obj V n ≃+ Sheaf.H.{0} G n) x) := by
  intro n
  induction n with
  | zero =>
    intro G G' _ _ φ x
    exact GlobalTheory.T.cech_h0_pull_compat f V hV U hU τ hτ φ x
  | succ n ih =>
    cases n with
    | zero =>
      intro G G' hG hG' φ x
      obtain ⟨α, hα⟩ := GlobalTheory.CompanionTheory.CechLift.exists_injectiveSequence_lift f φ
      rw [← hα]
      exact GlobalTheory.T.cech_connecting_pull_natural f V hV U hU τ hτ (S := injectiveSequence G) (S' := injectiveSequence G')
        (injectiveSequence_shortExact G) (injectiveSequence_isCechShortExact hCY V hVB G hG)
        (injectiveSequence_cechAcyclic G V) (injectiveSequence_shortExact G')
        (injectiveSequence_isCechShortExact hCX U hUB G' hG') (injectiveSequence_cechAcyclic G' U) α x
    | succ m =>
      intro G G' hG hG' φ x
      obtain ⟨α, hα⟩ := GlobalTheory.CompanionTheory.CechLift.exists_injectiveSequence_lift f φ
      rw [← hα]
      exact GlobalTheory.T.cech_sheaf_cohomology_pull_compat f V U τ hτ (S := injectiveSequence G) (S' := injectiveSequence G')
        (injectiveSequence_shortExact G) (injectiveSequence_isCechShortExact hCY V hVB G hG)
        (injectiveSequence_cechAcyclic G V) (injectiveSequence_shortExact G')
        (injectiveSequence_isCechShortExact hCX U hUB G' hG') (injectiveSequence_cechAcyclic G' U) α m _ _
        (fun y => ih (injectiveSequence_goodAcyclic hCY G hG)
          (injectiveSequence_goodAcyclic hCX G' hG') α.τ₃ y) x

end GlobalTheory.CompanionTheory.CechLerayPull
