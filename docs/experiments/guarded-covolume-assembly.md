# Experimental guard-parametric covolume assembly

**Status: implemented source candidate, not Lean-compiled or kernel-certified.** This
branch adds a theorem rather than replacing either existing proof body.

See [proof atlas PR #2](https://github.com/laurajoyhutchins/riemann-hypothesis-lean/pull/2)
for the background and [research PR #1](https://github.com/laurajoyhutchins/riemann-hypothesis-lean/pull/1)
for existing full-source graphs and census tooling. This is a separate focused
proof experiment, based on the unmodified main branch.

## Mathematical implementation

File:
`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/CovolumeGuardedAssembly.lean`.

The original `GlobalTheory.CovTop.Assembly.covolX_of_steps` and newer
`covolX_of_lift_bounds_and_coreLe` both assemble eight local estimates
via the **same** existing `lcv_le` lemma, and both choose a uniform cutoff
using `exists_loss_le`. Their final propositions differ only by the
admissibility guard supplied to the eventual-point quantifier.

The candidate introduces `PointAdmissibility`, `EventuallyUnder`,
`LiftsUnder` and `CovolumeUnder`, then proves:

```lean
covolume_of_guarded_steps (guard : PointAdmissibility) :
  LiftsUnder guard GramAt →
  LiftsUnder guard RecAt →
  LiftsUnder guard CutAt →
  LiftsUnder guard BadAt →
  LiftsUnder guard LamAt →
  LiftsUnder guard SizeAt →
  LiftsUnder guard CoreAt →
  LiftsUnder guard LowAt →
  CovolumeUnder guard
```

The notation above abbreviates the index and bound arguments. The source
file contains the actual fully dependent Lean statement and proof.

The additional theorem
`covolX_of_steps_from_guard` is declared with the **exact original
source-written target type**
`Gram → Rec → Cut → Bad → abelian₂ → Size → CoreLe → Low → CovolX`.
The companion `covolX_of_lift_bounds_from_guard` has the original
third-place theorem's eight arrow domains and `CovolumeBoundOfX` result.

The intended specializations are `guard := fun _ _ _ _ p => RowsT p` and
`guard := fun _ _ _ _ p => RowsTAlt p`, respectively. This does **not**
postulate or claim `RowsTAlt p → RowsT p`; the older and newer
realization hypotheses remain distinct.

The new theorem intentionally reuses the original numerical `lcv_le`
and `exists_loss_le`. It duplicates no proofs of local height,
arithmetic positivity, or theta-lift constructions.

## Exact-head verification gate

The following commands **have not yet been run on the actual RH
toolchain**. The current environment does not contain the pinned Lean
compiler or the full repository checkout.

```sh
git rev-parse HEAD
cat lean-toolchain
lake exe mathlib/cache get
lake build Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CovolumeGuardedAssembly
lake env lean checks/CovolumeGuardedAudit.lean
```

The audit imports both original and new theorems, displays their
types and prints transitive axiom dependencies. Verify actual equality
of elaborated types and universe parameters in the loaded Lean
environment, not just textual similarity. If either specialization
fails, keep the complete error and determine whether the defect is
syntax, `Closed` elaboration, dependency indexing, type inference,
or genuinely different propositions. Do not fill proof holes with
`sorry` or axioms.

`.github/workflows/rh-guarded-covolume-gate.yml` carries this real
source-build gate. It is **opt-in** while the PR is a draft to avoid
expensive, unproductive 175k-module builds. Marking the PR ready for
review or explicitly dispatching the workflow enables its heavy job.
A passing source build is necessary but is not independent RH proof
verification.

## Decision after compilation

1. Verify both new specializations against their old theorem heads and
   audit their axioms and implicit universes.
2. If accepted, replace **only** the two duplicated assembly proof
   bodies with the corresponding specializations in a follow-up commit.
3. Measure physical source-line savings, target module imports and
   rebuild time. The new generic abstraction must be counted against
   deleted lines; a negative net saving is not compression.
4. Independently compare the separate, more complicated `topCovolG`
   wrappers. Their intermediate lemma families differ and may not be
   reducible to the shared assembly proof.
5. Retain the final five theorem types and a separate full-rebuild/
   kernel-verification gate before merging into main.

The import-chain experiments and heavy kernel-export work already
live in PR #1 and are **not reimplemented here**.
