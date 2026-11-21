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

## Community build-infrastructure adoption boundary

The reference implementation is
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis/tree/8ec38f92ac54b5c91bc07f4f6f88ea61691b7975)
at pinned commit `8ec38f92ac54b5c91bc07f4f6f88ea61691b7975`.
See [community cache documentation](https://github.com/leanprover-community/riemann-hypothesis/blob/8ec38f92ac54b5c91bc07f4f6f88ea61691b7975/verification/CACHE.md),
[PR build workflow](https://github.com/leanprover-community/riemann-hypothesis/blob/8ec38f92ac54b5c91bc07f4f6f88ea61691b7975/.github/workflows/build-pr.yml),
and [clean Comparator instructions](https://github.com/leanprover-community/riemann-hypothesis/blob/8ec38f92ac54b5c91bc07f4f6f88ea61691b7975/README.md).

The immediate port uses the community's **five-field cache-input identity
schema**, not its cache artifacts, publisher, or source build controller.
`tools/rh_ci_identity.py` writes a clean-Git receipt containing the committed
`src` tree identity, `lakefile.toml` SHA-256, dependency manifest SHA-256,
Lean toolchain and build-roots field, plus the same canonical SHA-256 fingerprint.
A documentation-only commit retains the fingerprint; changing the proof source,
toolchain or configuration invalidates it. Dirty or untracked proof sources
and ignored files under `src` are rejected. The receipt says
`proof_verified: false` and is never an authorization to restore or trust an
artifact. A matching digest authenticates input identity, **not proof validity**.

The five-field convention is compatible with the community's identity
calculation, but its published receipts are repository-scoped and its cache
service expects an exact source/configuration match. Our fork has changed
proof modules and a different lakefile. **No full community root cache is
declared compatible with our modified fork** merely because the toolchain
matches. Do not copy a cache map, patch repository fields, or re-label existing
`.olean` outputs to make it appear compatible.

The community's full pipeline also uses dedicated large Linux runners,
untrusted-PR sandboxing, durable interrupted-build recovery, immutable packed
artifacts, and an isolated publisher. Those capabilities require further
adaptation and verification before being enabled here. The community
documentation's recommended runner is about 128 GiB RAM with at least 250 GiB
free SSD; the normal hosted runners are not interchangeable. No storage
credentials or external publisher are configured by this change.

Code and proof redistribution permissions must be checked before bulk
vendoring the upstream scripts or proof artifacts. This change uses a small
independently implemented interface and links to the upstream implementation.

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

## Experimental persistent warm Lake recovery (NOT a verification gate)

`tools/rh_ci_durable_build.py` is a **small, source-bound recovery
adapter**, derived from the community's architectural distinction between
retaining completed build work and independently validating it. See their
[`ci-build.py`](https://github.com/leanprover-community/riemann-hypothesis/blob/8ec38f92ac54b5c91bc07f4f6f88ea61691b7975/scripts/ci-build.py)
and [`RecoverCompleted.lean`](https://github.com/leanprover-community/riemann-hypothesis/blob/8ec38f92ac54b5c91bc07f4f6f88ea61691b7975/scripts/cache-bootstrap/RecoverCompleted.lean).
It intentionally **does not** copy upstream's repository-specific publisher,
the source runtime sandbox, its verified artifact map, or its stock
no-build/raw-output recovery implementation. Do not describe this as a
replacement for that larger system.

On a dedicated persistent and externally sandboxed Linux runner, prepare
the pinned Mathlib dependency cache separately, then execute (example;
the sandbox must already be configured by the operator):

```bash
python3 tools/rh_ci_durable_build.py \
  --workspace /persistent/rh/checkout \
  --state-root /persistent/rh/checkpoints \
  --module Main \
  --acknowledge-isolated-runner
```

The checkout and state directory **must survive between runs**; both must
be owned by the runner user. The controller requires committed clean proof
source and pinned input files, locks the workspace against concurrent
controller runs, records a canonical `input_fingerprint`, runs `lake build
Main` with `LAKE_ARTIFACT_CACHE=false`, and writes an fsync-backed
checkpoint and append-only log. Failed and gracefully interrupted commands
retain any raw Lake work **at the same workspace path**. Retry the exact
same command to have stock Lake decide which outputs need rebuilding.
There is no custom `.olean` acceptance path and no artifact publication.

This is a **warm build** only: `build_succeeded` means the invoked Lake
process exited 0, not independent kernel validation, axiom closure or proof
preservation. The emitted checkpoint always records `proof_verified: false`.
Never run candidate-controlled code on a host holding publishing secrets.
The `--acknowledge-isolated-runner` argument is a mandatory human/operator
assertion; it **does not establish sandboxing**. Do not use the experimental
wrapper in `pull_request_target` or on an unisolated self-hosted runner.

The default is fail closed across changed source/configuration inputs in the
same persistent workspace. `--allow-cross-input-reuse` explicitly delegates
invalidation to stock Lake for *untrusted warm iteration only*, never proof
certification. Interrupted `SIGTERM` is journaled as `interrupted`, but
`SIGKILL` or host crash may leave an `building` journal and active child
processes. Such an orphan is **not automatically adopted**; the operator
must independently establish quiescence and move aside the old workspace
before starting a clean candidate. The controller does not provide the
community's quiescence proof, bounded resource cgroups, portable LTAR
packaging, uploader, distributed cache, or source-recovery completeness.
Those are still required before enabling production self-hosted jobs.

No new expensive CI runner is configured by this experiment. The
`test_rh_ci_durable_build.py` fixtures exercise partial-work survival,
SIGTERM/resumption, cross-input refusal, locked workspaces and metadata
tampering with a fake Lake command. The fixtures test the controller, not
Lean's actual trace/hash validation nor mathematical theorems.

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
