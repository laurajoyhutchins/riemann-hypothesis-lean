# From character nonvanishing to the final RH/GRH statements

**Evidence:** direct reading of Lean source declarations on the repository's default branch. Neither a full build nor independent kernel replay has been performed for this document.

## What the major hypothesis says

[`Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean`](../../src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean) defines `UpperTheory.EveryCharacter : Prop` as

```lean
∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
  1 / 2 < s.re →
  (χ ≠ 1 ∨ s ≠ 1) →
  DirichletCharacter.LFunction χ s ≠ 0
```

This is a nonvanishing assertion strictly to the right of the critical line, with the trivial-character pole case excluded. It is the central *analytic interface* between the much larger automorphic/Galois construction and the short final arguments.

## How it implies RH

[`Formalism/GammaFactorNonvanishing/CritLine.lean`](../../src/Formalism/GammaFactorNonvanishing/CritLine.lean) contains

```lean
theorem Formalism.VW.rh_of_every (h : UpperTheory.EveryCharacter) :
    RiemannHypothesis :=
  Formalism.VW.rh_of_right fun s hs hs1 => by
    have := h 1 (1 : DirichletCharacter ℂ 1) s hs (Or.inr hs1)
    rwa [LFunction_modOne_eq] at this
```

The step at modulus one identifies the trivial Dirichlet L-function with `riemannZeta`, converting the universal character hypothesis into zeta nonvanishing for `Re(s) > 1/2` away from `s = 1`.

[`Formalism/GammaFactorNonvanishing/RhOfRight.lean`](../../src/Formalism/GammaFactorNonvanishing/RhOfRight.lean) then handles the opposite side of the critical line using `riemannZeta_one_sub` (the functional equation relating `s` and `1-s`). Its proof explicitly handles the gamma, cosine, and trivial-zero exceptional factors. On the line, the conclusion is immediate. That short final theorem does not itself establish right-half-plane nonvanishing: it **assumes** it.

A second source-level proof of the same implication appears as `UpperTheory.riemannHypothesis_of_everyCharacter` in [`CharacterBoxes/RiemannHypothesisOfEveryCharacter.lean`](../../src/Development/AutomorphicArithmetic/CharacterBoxes/RiemannHypothesisOfEveryCharacter.lean), which instead uses `completedRiemannZeta_one_sub`. These are **two distinct proof implementations** of the same logical reduction, not automatically a safe deletion opportunity: consumers, imports and elaborated dependencies must be checked before consolidation.

## How it implies the character zero-location results

[`Formalism/GammaFactorNonvanishing/CritLine.lean`](../../src/Formalism/GammaFactorNonvanishing/CritLine.lean) also defines `Formalism.VW.critLine` for primitive characters. For a hypothetical zero in `0 < Re(s) < 1/2`, it invokes the functional equation of the *completed* L-function, establishes nonvanishing of the gamma factor in the relevant half-plane, and obtains a zero for the inverse character at `1-s`, which lies to the right of the critical line. That contradicts `EveryCharacter`. For a zero already right of the critical line, the contradiction is direct.

[`Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean`](../../src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean) supplies the **all-character** extension:

- `Claim.factor_ne_zero` shows Euler factors introduced by a conductor/level change do not vanish in `Re(s)>0`, using a norm strictly below one.
- `Claim.prim_zero` moves a zero of an imprimitive L-function to its associated primitive character.
- `Claim.prim_reflect` applies the primitive-character functional equation.
- `Claim.strip` combines these with right-half-plane nonvanishing to establish `Claim.Strip`.
- `Claim.zeta` treats zeta zeros via modulus-one identification and completed-zeta reflection.
- `Claim.zeta_iff` is declared as `Zeta ↔ RiemannHypothesis := Iff.rfl`, making the relationship between these two *definitions* explicit.

These are inspectable source claims, not assertions of independent verification.

## The final dependency picture

```text
UpperTheory.EveryCharacter
  ├─ Formalism.VW.rh_of_every ──────────> RiemannHypothesis
  │     └─ Formalism.VW.rh_of_right
  ├─ Formalism.VW.critLine ─────────────> primitive-character zeros on Re(s)=1/2
  └─ Claim.strip / Claim.zeta ──────────> all-character strip & zeta claims
       └─ Claim.factor_ne_zero / prim_zero / prim_reflect
```

This is a human-readable graph of the inspected *direct source path*. It is not the transitive elaborated dependency graph for `Main`.

## Questions for verification or compression

1. Can the two RH-from-`EveryCharacter` conversion proofs be unified with the same theorem statement and shorter import closure?
2. Which branch does each of the five final declarations actually use, after elaboration? Why is the second RH conversion included in the literature bridge?
3. Does a shared functional-equation/reflection lemma eliminate repeated gamma-factor arguments without widening axioms?
4. If these lemmas are deduplicated, are the savings meaningful in **net source lines**? These final analytic proofs are short; they are unlikely to explain millions of lines of duplication.

Continue at [the literature/theta-lift bridge](literature-bridge.md) for the hard part of the proof, or return to [navigation](../proof-navigation.md).
