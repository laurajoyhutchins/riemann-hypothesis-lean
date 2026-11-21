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
