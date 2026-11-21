# RH proof visualization: use upstream Lean Graph

**Viewer and dependency extractor:** [patrik-cihal/lean-graph](https://github.com/patrik-cihal/lean-graph) ([open viewer](https://patrik-cihal.github.io/lean-graph/)). We do not maintain an alternative graph renderer or expression-index service in this PR. The small `rh_lean_graph.py` wrapper only pins and retrieves upstream `DependencyExtractor.lean`, verifies its Git blob, prepends `import Main`, and issues one upstream extraction command per selected theorem.

## Use

On a checkout of the RH source with its pinned Lean toolchain and Mathlib dependencies:

```bash
lake exe cache get
lake build Main
python3 tools/rh_lean_graph.py --depth 2
lake env lean analysis/RHLeanGraph.lean
```

Five `<theorem>.json` files are created in the current working directory. Open any one at https://patrik-cihal.github.io/lean-graph/ via **Open extracted data**. The default roots are the five declarations in `src/Main.lean`. To focus on the common proof root instead:

```bash
python3 tools/rh_lean_graph.py --root UpperTheory.FinalTheorems.everyCharacter --depth 3
lake env lean analysis/RHLeanGraph.lean
```

The wrapper pins upstream commit `12fe82c12a41a827265bac725351cade3511d28a`, extractor Git blob `2cb37f37f01427086d2bf53a6fc8bdf4a8daaa69`. If retrieving it is not possible, download this exact version elsewhere and pass `--extractor path/to/DependencyExtractor.lean` (the same blob check applies). No upstream source is committed to this repository.

## What the diagram does and does not show

Lean Graph's regular extractor traverses **theorem proof-body constant references** to a specified breadth-first depth. It excludes instances by default and intentionally limits graph depth. Its default extraction is not a complete elaborated expression AST, a five-root transitive closure census, or a proof certification. Increasing depth may be very expensive on RH's enormous environment, and the upstream viewer currently loads a bounded JSON graph rather than lazily querying all exported expressions.

The independent `tools/export_exact_graph.py` in RH [research PR #1](https://github.com/laurajoyhutchins/riemann-hypothesis-lean/pull/1) remains available for exact checked-expression dependency analysis. That is not a replacement viewer and should remain separate. The full RH source has not been rebuilt, the complete checked graph has not been generated, and no changed theorem has been independently kernel-verified by this visualization integration.

## Smoke tests

```bash
python3 -m unittest discover -s tools -p 'test_rh_lean_graph.py' -v
```

These tests check source generation and tamper refusal, not a full Lean build. The real Lean invocation is intentionally explicit because it imports the complete RH environment.
