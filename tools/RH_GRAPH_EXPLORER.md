# RH declaration dependency visualization (upstream Lean Graph)

Use [patrik-cihal/lean-graph](https://github.com/patrik-cihal/lean-graph) and its [browser viewer](https://patrik-cihal.github.io/lean-graph/). No fork of its extractor, converter, database, renderer, or expression viewer is maintained here. The integration pins the exact upstream [`DependencyExtractor.lean`](https://github.com/patrik-cihal/lean-graph/blob/12fe82c12a41a827265bac725351cade3511d28a/static/DependencyExtractor.lean) Git blob `2cb37f37f01427086d2bf53a6fc8bdf4a8daaa69`.

## Why a single pinned upstream correction is necessary

The pinned upstream `getConstantBody` calls `ConstantInfo.value?` without an argument. The actual [Lean 4.33.1 implementation](https://github.com/leanprover/lean4/blob/v4.33.1/src/Lean/Declaration.lean) returns `none` for theorem proofs unless `allowOpaque := true`. Unmodified upstream extraction therefore silently emits theorem nodes with no theorem dependencies. A genuine `MiniMain.entry` smoke initially reproduced this bug.

The wrapper first verifies the **unmodified** upstream Git blob, then applies exactly one replacement: `let constValue := constInfo.value?` becomes `let constValue := constInfo.value? (allowOpaque := true)`. It refuses to proceed if the replacement point is missing or duplicated. This is a one-line correction to the upstream extractor, **not** an independent traversal, graph format, or viewer. It should be retired once an upstream fix is merged and pinned. The validation manifest records the correction. It still does not recover type-only dependencies, filtered instances, or proof AST structure.

## Source roots

The five top-level declarations are in `src/Main.lean`, which imports `Statements` and `Supplements.Kernels.MainTheorems`:

| Root | Proof expression in `src/Main.lean` |
|---|---|
| `riemannHypothesis` | `rhOfAll` |
| `riemannZeta_eq_zero_re` | `rhOfAll` |
| `LFunction_ne_zero_of_half_lt_re` | `allChi` |
| `LFunction_eq_zero_re` | `claimAll.2.1` |
| `LFunction_eq_zero_re_of_isPrimitive` | `critAll` |

These are **source-inspected names**, not a fresh `Main.olean` resolution receipt.

## Real RH extraction from an already built environment

Run in the RH repository root. For the project's pinned toolchain and dependency manifest, use the existing community build/cache infrastructure to prepare a trusted build. Do **not** treat an old cache as independent proof verification.

```bash
# Required once, or satisfied by a provenanced reusable Main.olean build:
lake exe cache get
lake build Main

# Choose an explicit BFS depth. Depth 2 is a neighborhood, not the full closure.
python3 tools/rh_lean_graph.py --depth 2
/usr/bin/time -v -o analysis/lean-graph-time.txt \
  lake env lean analysis/RHLeanGraph.lean
python3 tools/validate_rh_lean_graph.py --depth 2 \
  --source-revision "$(git rev-parse HEAD)" \
  --output-dir analysis/lean-graph-json
```

This produces six canonical JSON files (five single-root graphs and `RH-combined.json`) plus `manifest.json`. The manifest records source revision, upstream commit/blob, hashes, sizes, node and edge counts, and external references. The real upstream functions generate every graph; Python only checks the emitted viewer schema and sorts the JSON for reproducible inspection.

To demand that **all references emitted by the upstream extractor** have included nodes, increase `--depth` and rerun the entire command, then add `--require-closed` to the validator. A failure is evidence that the requested depth leaves a boundary. A success establishes only *closedness under emitted references*. Upstream's regular extractor follows proof-value references, excludes instances by default, and does not traverse type-only references. It suppresses some BFS errors, which the combined driver rechecks at each expanded node before publishing. Neither the emitted-edge closure nor that recheck establishes complete Lean semantic dependency coverage or all source/build dependencies.

For focused exploration, pass repeatable `--root` arguments to **both** scripts. The `--module` option on the generator enables genuine-compiler compatibility tests against small standalone Lean modules. `--no-combined` is for narrow debugging; omit it for auditable five-root runs. The source driver explicitly checks root names. The validator refuses duplicate nodes, wrong schemas, absent/non-theorem roots, mismatches between the union and individual files, and dangling references when `--require-closed` is used.

Open one of the validated `.json` files with **Open extracted data** in the [upstream viewer](https://patrik-cihal.github.io/lean-graph/). The viewer source expects exactly `name`, `references`, `constCategory`, and `constType`. Loading huge graphs interactively is not demonstrated; its current Rust/egui renderer builds and simulates an in-memory graph, without lazy graph loading. JSON validation verifies the loader's schema, **not** a successful browser interaction or frame-rate measurement.

## CI tiers and evidence boundaries

The `rh-lazy-graph.yml` PR job runs Python tests and then builds `MiniMain` with pinned Lean 4.33.1, invokes the **actual** pinned upstream extractor, validates its JSON, and uploads a small graph and `/usr/bin/time -v` receipt. It does not fetch Mathlib or build the RH project. This genuine tiny Lean check is a compatibility gate, not an RH graph.

The full RH workflow is deliberately **not** a pull-request smoke job. Reuse the community's self-hosted resumable build infrastructure and its verified source identity receipts, then run the extraction commands above in that already built environment. Preserve `Main.olean` provenance, the input Git tree and toolchain/Mathlib revision; archive the resulting JSON and `lean-graph-time.txt`. Run an independent clean proof verification separately. Without a built `Main.olean`, there is no honest full-RH graph artifact.

## What remains unverified

A complete extracted five-root RH graph, a live large-graph viewer load, wall-time/peak-RSS on RH, full declaration type-plus-value closure, and full proof syntax/Expr AST extraction. Upstream normal JSON cannot certify unused Lean source files, mathematical proof equivalence, or preservation of the five final theorem types. The separate `export_exact_graph.py` research stream addresses a different, checked-expression traversal problem; do not delete it or reintroduce the previously removed viewer and adapter.


## Reuse a *completed* community build without rebuilding

The optional [retained-build graph workflow](../.github/workflows/rh-graph-retained-build.yml) is manual and runs only on a self-hosted runner with the `rh-build` label. Select a source-matching successful checkpoint at `$RH_CI_STATE_DIR/failed-work/run-*/checkpoint.json`, not an original or stale build. Supply that checkpoint path and an explicit BFS depth via the workflow's `workflow_dispatch` inputs.

The small `tools/rh_graph_postbuild.py` preflight compares the retained checkpoint's source Git tree, pinned Lean toolchain, manifest and lakefile hashes to the checkout; requires a *staged successful* community build; and checks `Main.olean`, its Lake trace, mapped archive and artifact hashes. **Before extraction**, it additionally invokes the pinned community controller's own `verify_snapshot` to compare **all** retained `src/` and pinned configuration bytes against the current checkout's Git blobs. This is an intentionally more expensive source-provenance audit, not another Lean build. Different *tooling-only* commits can reuse the same source-matching build. Unfinished, mismatched, tampered, or missing compiled evidence fails closed.

For extraction the script loads the pinned community `scripts/ci-build.py` **as the sandbox provider**. It runs the pinned upstream Lean Graph driver within that existing Bubblewrap environment and uses `lake env` to establish imports, switching into the writable retained result directory for JSON. There is no new Lean compiler, graph traversal, cache controller, or local viewer. The standard validator emits the five root files, combined JSON, SHA-256 manifest, and resource receipt. An explicit smoke test checks the source-admission logic, but **the retained-build end-to-end command has not yet run against the full RH environment**.

Run the preflight without touching Lean:
```bash
python3 tools/rh_graph_postbuild.py \
  --candidate . --community community-harness \
  --checkpoint "$RH_CHECKPOINT" \
  --state "${RH_CI_STATE_DIR:-$HOME/.local/share/riemann-build-state}" \
  --extractor /dev/null --output analysis/lean-graph-json \
  --preflight-only
```

The `community-harness` checkout must be pinned to `79c751e0b0a5ea3bbfc20198c852fa85f28661e6`; the manual workflow verifies this and the upstream Lean Graph blob before actual execution. The postbuild code compares the exact trusted controller script's Git blob before importing it. Do not run an arbitrary `ci-build.py` on the self-hosted runner.

The workflow exposes `depth` and `require_closed`. At the default depth 2 it produces a bounded neighborhood with an explicitly recorded reference frontier. Set `require_closed: true` to reject any unresolved *emitted* reference, but even success does not establish type/instance closure or proof AST coverage. GNU `time` measures peak RSS and wall time for the **actual** sandbox/Lake/Lean subprocess, separately from the full-source snapshot audit. If upstream extraction fails or emitted-edge validation refuses a graph, the workflow still uploads `failure.json`, available Lean logs, and the time receipt; it never calls a partial graph complete.

A verified graph or closed emitted-edge neighborhood is **not** a fresh Lean proof check, not a theorem-type comparison, and not evidence that source-only modules can be pruned. The manual workflow requires both a suitable registered runner and an already completed matching source build. No completed RH extraction is implied by the existence of this entry point.


## Integration branch and removal of obsolete viewer code

[PR #17](https://github.com/laurajoyhutchins/riemann-hypothesis-lean/pull/17) now targets `research/declaration-census-20261120`, not the archived feature branch used for the original PR #15. The integration explicitly removes `rh_graph_explorer.py`, `rh_graph_viewer.html`, `export_lean_graph.py` and their two tests from that active branch. It preserves the separate `export_exact_graph.py` kernel-expression research analyzer. The [reconciled diff](https://github.com/laurajoyhutchins/riemann-hypothesis-lean/compare/research/declaration-census-20261120...feature/rh-lean-graph-real-extraction-20261121) should contain only graph tools, documentation, and CI, **no proof-source edits**. Re-run the fast checks against this final target tree before merging; the full modified RH extraction remains a separate manually dispatched obligation.


### Command for a source-matching retained RH build

The graph-only job can also be run directly on a correctly provisioned build runner using the retained successful checkpoint printed by the trusted community controller:

```bash
# After checking out the graph integration and pinned community-harness scripts:
export RH_CHECKPOINT=/absolute/path/to/failed-work/run-.../checkpoint.json
export RH_CI_STATE_DIR="${RH_CI_STATE_DIR:-$HOME/.local/share/riemann-build-state}"
mkdir -p analysis
curl -fsSL \
  https://raw.githubusercontent.com/patrik-cihal/lean-graph/12fe82c12a41a827265bac725351cade3511d28a/static/DependencyExtractor.lean \
  -o analysis/DependencyExtractor.upstream.lean
python3 tools/rh_graph_postbuild.py \
  --candidate . --community community-harness \
  --state "$RH_CI_STATE_DIR" --checkpoint "$RH_CHECKPOINT" \
  --extractor analysis/DependencyExtractor.upstream.lean \
  --depth 2 --output analysis/lean-graph-json
```

The script validates the pinned upstream extractor's actual Git blob; arbitrary downloads cannot pass. For a fail-closed *emitted-edge* closure attempt, add `--require-closed` and increase `--depth` as needed. A failed attempt preserves `analysis/lean-graph-json/failure.json` and available receipts, **not** a complete graph. The existing viewer can open each validated `.json` through **Open extracted data**; RH-scale responsiveness has not been verified.

GitHub Actions manual `workflow_dispatch` requires the workflow to be installed on the repository's default branch. While this job remains solely on the draft feature/research branch, its source is available, but its manual dispatchability through the default Actions UI is not established. Running the command directly avoids confusing workflow registration with source-build readiness.


## One-shot original community RH build and graph attempt (2026-11-22)

A one-shot source-matching full build has been explicitly requested. The fork's existing community workflow remains authoritative and delegates to unchanged upstream `ci-prepare.py` and `ci-build.py`, including the community's durable build/cache work and sandbox. A narrow `push` trigger for `feature/rh-lean-graph-real-extraction-20261121` is additionally gated by the exact head-commit marker `[run rh full build 20261122]`; ordinary subsequent PR pushes, graph tests, and docs changes do **not** run the expensive build.

If a registered isolated `rh-build` runner exists, the one-shot job performs its pinned source/manifest checks, prepares the original community cache, and runs the **stock** community Lean full build. Only after a successful `staging/receipt.json` does it read the retained work checkpoint, verify the source tree, invoke pinned upstream Lean Graph at depth 2, and upload the five root JSONs, combined JSON and measured extraction receipts (or an explicit failed extraction receipt). If it fails, do not label the job success or treat cached build output as independent kernel proof verification.

The job is constrained by the community wrapper's existing 96 GiB configurable systemd memory limit, default eight parallel workers, 12 GiB disk reserve and 24-hour GitHub Actions timeout. It is **not guaranteed to start**: absence of an eligible self-hosted runner leaves it queued. This document is not a claim that such a runner exists or the fork has ever completed a full proof build. The workflow is deliberately branch-scoped and event-gated rather than a recurring full-build CI obligation. The research PR remains draft while proof verification and performance obligations are open.
