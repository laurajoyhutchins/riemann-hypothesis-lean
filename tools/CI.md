# CI cost policy for the RH minimization experiment

The RH source corpus contains about 175,000 Lean modules. Ordinary analysis-tool
edits must not launch a multi-hour read of the same immutable original kernel
export. Equally, fast analysis jobs must never be represented as proof checks.

## Automatically executed on relevant PRs

- `rh-minimization-tools.yml`: **all** deterministic Python tool tests.
  Sparse checkout of `tools/`; no 1 GB proof-source checkout.
- `rh-census-smoke.yml`: pinned Lean v4.33.1 mock-environment declaration
  census. It does **not** import or verify the RH development.
- `rh-export-closure.yml` and `rh-exact-graph.yml`: small unit and official
  exporter-format fixture checks. They do **not** download the full original
  proof export on PRs.
- `rh-source-impact.yml`: on a change to `src/**` or pinned build inputs,
  builds a reverse source-import impact **candidate** set and verifies the
  unchanged five top-level theorem source lines. Its output is **not**
  a complete Lean elaboration dependency graph or proof verification.

The source-import planner deliberately invalidates every local module when
`lakefile.toml`, `lake-manifest.json`, `lean-toolchain` or a non-Lean source
input changes. Deletions appear as absent changed modules. Unknown import
syntax and unresolved possibly local imports fail closed. Consumers must not
claim that these source-import candidates are a safe set of modules to build:
Lean macros, elaborators, dynamic inputs and imported environment changes may
create additional dependencies.

## Direct community CI integration

The community CI is **not reimplemented in this fork**. The original repository
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
is pinned as Git submodule `upstream/riemann-hypothesis-community` at
[`79c751e0b0a5ea3bbfc20198c852fa85f28661e6`](https://github.com/leanprover-community/riemann-hypothesis/commit/79c751e0b0a5ea3bbfc20198c852fa85f28661e6).
The [integration workflow](../.github/workflows/rh-community-upstream.yml)
checks out this exact upstream commit and invokes **its actual**
`scripts/ci-prepare.py` and `scripts/ci-build.py` without modifying their
source. It also runs the upstream preparation, publication-trust, and runner
unit tests as inexpensive automatic PR checks.

**Input compatibility verified at integration:** our fork's
`lake-manifest.json` and `lean-toolchain` bytes agree exactly with the
upstream community version. The fork's `lakefile.toml` contains the original
root libraries/configuration; the upstream copy additionally contains
its own cache executable and publication service. The upstream controller
snapshots the fork's actual `src`, lakefile, manifest and toolchain. It
validates those inputs, restores the upstream original module baseline
under its own input-hash checks, then executes *stock Lake* in its
Bubblewrap sandbox with its **own** durable interrupted-work and
finished-module recovery logic. Incompatible original artifacts are
invalidated by Lake; exact restored archives alone do not prove the edited
source correct.

A manual `workflow_dispatch` full-build job requires a registered isolated
self-hosted Linux runner labeled `rh-build` (and `systemd-run` user-manager,
Bubblewrap, pinned Lean tooling, and a large persistent disk). Without a
matching runner that job cannot execute. It is not an automatic PR proof gate
or something that runs on a lightweight hosted runner. The community
[runner guidance](https://github.com/leanprover-community/riemann-hypothesis/blob/79c751e0b0a5ea3bbfc20198c852fa85f28661e6/verification/CI-RUNNERS.md)
recommends roughly 128 GiB RAM and at least 250 GiB free disk.
The exact full-build job has **not** been observed to complete on the fork.

No community publishing credentials or the upstream `publish-ci-cache.py`
publication workflow are invoked: those bind explicitly to
`leanprover-community/riemann-hypothesis` and must not be relabeled.
The fork uploads small local evidence only; incomplete results stay on the
persistent runner and may be recovered by the actual upstream controller.
Build output remains an accelerator, not independent proof verification.

The older fork-side recovery experiments have been retired. The exact files
deleted are `rh_ci_durable_build.py`, `rh_ci_recover.py`,
`RHRecoverCompleted.lean`, their tests, the stock-recovery smoke harness
and workflow. Their [experimental test evidence](https://github.com/laurajoyhutchins/riemann-hypothesis-lean/pull/8)
is historical, but the community now owns the authoritative implementation
and future improvements. `rh_ci_identity.py` stays as a small,
fork-specific read-only source/configuration identity adapter already used
by the source impact gate; it does **not** implement build or recovery logic.

Upstream changes must be adopted by reviewing a new pinned submodule commit,
not by copying or independently editing upstream scripts. The submitted
proof source has no declared redistribution license; the submodule preserves
upstream ownership and history rather than vendoring a second copy.

## Focused Lean proof gate on review-ready candidates

The Harris–Taylor four-module proof build (`rh-pullback-proof-gate.yml`) is
expensive source-derived Lean elaboration, unlike the synthetic checks above.
For a draft PR, its job is **skipped**, not passed. It runs when a PR with
matching proof changes is marked ready for review, on subsequent updates while
ready, or via explicit workflow dispatch. Cancellation is enabled only for
superseded PR runs, not intentionally dispatched milestone runs. This prevents
rapid draft commits from repeatedly abandoning large Mathlib preparation.

This focused gate, even when green, covers four selected modules rather than
all five final RH theorem roots. Its runtime and cache behavior still need
measured tuning before generalizing to the whole development. The workflow
now uses the community's **clean-verification invocation**:
`LAKE_ARTIFACT_CACHE=false`, `LEAN_ABORT_ON_PANIC=1`, and
`lake exe mathlib/cache get` (not project-root `lake exe cache get`).
It does not run `lake update` or rewrite the pinned manifest, and it
records the source/configuration fingerprint both before and after fetching
Mathlib. A successful focused build still does **not** check all five theorems.

## Explicitly dispatched research/milestone jobs

- `rh-census-smoke.yml` full-source-inventory job: count all source lines and
  verify the prune contract.
- `rh-structural-profile.yml`: structural survey of every local Lean file.
- `rh-export-closure.yml` published-proof-census: verified download and
  inventory of **the published original** kernel export.
- `rh-exact-graph.yml` published-proof-five-root-graph: verified download and
  five-root graph traversal of **the published original** kernel export.

These latter two jobs share an immutable SHA-256-pinned upstream artifact, but
do not verify the source produced by this branch. They should only be run to
answer a new research question, not as a default response to each tooling edit.
Their auto PR smoke jobs remain active.

## Reproducibility: byte identity is not proof identity

The community's [verification notes at pinned revision](https://github.com/leanprover-community/riemann-hypothesis/blob/8ec38f92ac54b5c91bc07f4f6f88ea61691b7975/verification/NOTES.md)
explain that Lean 4.33.1 records absolute source filenames in some serialized
`.olean` linter diagnostics. So two fresh builds from equivalent proof sources
in *different directories* may have different `.olean` SHA-256 values.
A cache receipt must bind and validate the actual artifact bytes it stores;
an independent proof-reproducibility comparison should instead compare
checked target types and source-derived proof exports under a pinned kernel.
This is not a license to ignore actual compiler errors or failed kernel checks.

## Retired recovery prototypes

Our two earlier attempts to independently implement the community's
persistent warm-build checkpoints and stock Lake recovery have been removed
from active code and workflows. Reuse the pinned upstream controller above
instead; do not reintroduce a parallel cache publisher or recovery runner.

## Required future verification tier (NOT implemented by this CI change)

For any proof-source refactor before a claim of preservation or a trusted merge:

1. Build changed modules **and their actual elaboration-dependent dependents**
   with the original pinned Lean and Mathlib on a sufficiently provisioned
   machine, keeping validated incremental `.olean` reuse by content/inputs.
   A reverse import graph is useful planning data but cannot substitute for
   correct rebuild dependency tracking.
2. Clean-build the five final theorem roots without relying on a stale or
   incomplete artifact cache; verify all checked theorem types and universe
   parameters against an independently defined baseline. Keep the source hash
   and complete manifest in the receipt.
3. Audit the axiom closure of all five roots; reject additional axioms or
   proof holes. Independently replay the new source-derived proof export with
   a kernel checker and report the precise checker version and source commit.
4. Periodically make a *cold* end-to-end build and independent kernel replay
   from pinned source and dependencies. A full job failure due to resource
   exhaustion is **inconclusive**, not a proof rejection.

Do not mark the fast green checks as complete RH theorem verification.
No clean build or kernel replay of the modified proof source is claimed here.

## Next performance measurements

Collect queue delay, runner CPU-minutes, network bytes, checkout time,
cache hit/miss rates, per-module compile time, peak RSS, `.olean` reuse,
and number of modules invalidated per proof edit. Avoid comparing one fast
smoke check against an unmeasured full build. Cache keys must cover compiler
toolchain, Mathlib lock, relevant Lean options, all imported interfaces and
source inputs. Cached output is an accelerator, never independent evidence.
