# Character boxes: from a window to zero-free L-functions

**Source:** [`Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean`](../../src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean) and [`Imprimitive.lean`](../../src/Development/AutomorphicArithmetic/CharacterBoxes/Imprimitive.lean). The formulas below are read from source, not independently kernel-replayed.

## Two logically related names

`UpperTheory.EveryCharacter` and `Claim.HalfPlane` are both defined with the same displayed nonvanishing condition:

```lean
∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
  1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) →
  DirichletCharacter.LFunction χ s ≠ 0
```

The second definition is in [`CharacterBoxes/HalfPlane.lean`](../../src/Development/AutomorphicArithmetic/CharacterBoxes/HalfPlane.lean), alongside `Claim.Strip` and `Claim.Zeta`. This explains why [`Supplements/Kernels/MainTheorems.lean`](../../src/Supplements/Kernels/MainTheorems.lean) can use `allChi : UpperTheory.EveryCharacter` as the first component of `claimAll : Claim.HalfPlane ∧ Claim.Strip ∧ Claim.Zeta`. Whether Lean treats the two unfolded definitions as definitionally equal should be confirmed by elaboration; the source formulations are identical.

## A different route to all-character nonvanishing

The inspected `CharacterBoxes/EveryCharacter.lean` contains

```lean
theorem UpperTheory.Top.plugWin
    (hG : GlobalTheory.GLq.Green)
    (hV : UpperTheory.Top.VWin)
    (h : Nonempty (Hyps (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) DRS)) :
    Formalism.HC.ZeroFreeAll := ...

theorem UpperTheory.Top.plugAll
    (hG : GlobalTheory.GLq.Green)
    (hV : UpperTheory.Top.VWin)
    (h : Nonempty (Hyps (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) DRS)) :
    UpperTheory.EveryCharacter :=
  UpperTheory.Top.imprimitive (UpperTheory.Top.plugWin hG hV h)
```

Its visible proof chain is

```text
Green hypothesis + VWin + existence of closed/linked hypotheses
                         |
                  Top.plugWin
                         |
                   ZeroFreeAll
                         |
                Top.imprimitive
                         |
                  EveryCharacter
```

This is a second **navigation cut**, not a proven claim that the separate literature theorem calls `plugAll` directly. Locating the defining source and proof of `UpperTheory.Lit.every_character_of_theta_integrals_local_matching` is necessary to establish the exact relationship.

## Extending primitive characters

[`Imprimitive.lean`](../../src/Development/AutomorphicArithmetic/CharacterBoxes/Imprimitive.lean) proves `UpperTheory.Top.imprimitive`, converting `ZeroFreeAll` into universal L-function nonvanishing. It uses `χ.primitiveCharacter`, the level-change identity `LFunction_changeLevel`, and nonvanishing of every introduced Euler factor. For `Re(s)>1/2`, the norm of the positive-prime inverse power `p^{-s}` is strictly less than one, making the Euler factor nonzero.

The actual mathematical point is not a large tensor construction: the extension from primitive to imprimitive characters is a short analytic/algebraic postprocessing step. This is why the large-scale proof-compression investigation should concentrate upstream rather than on these compact final lemmas.

## What to inspect next

- The exact types of `GlobalTheory.GLq.Green`, `Formalism.HC.ZeroFreeAll`, and the `Hyps ... DRS` interface.
- Which theorem constructs the three arguments to `plugAll`, and whether this is the same route used by `every_character_of_theta_integrals_local_matching`.
- Whether `supplyChi` and `shapeWin` expose repeated constructions worth parameterizing, after checking their actual types.

See also [analytic reduction](analytic-reduction.md) and [literature bridge](literature-bridge.md).
