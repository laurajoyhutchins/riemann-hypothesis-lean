# RH kernel expression explorer

The five final theorem constants in `Main.lean` are the default roots. A Lean *syntax AST* (parser output) is different from the **checked proof-expression DAG** and different again from a **declaration-dependency graph**. This tool indexes the exact expression records of the official `lean4export` NDJSON stream, retaining immutable Expr IDs, names, mutual-group members and lossless JSON payloads. It does not invent the missing proof edges from the module-import graph.

This is a companion to `export_exact_graph.py`, not a replacement. Both use its expression-edge validation. The other tool computes the five-root reachable closures; this one supports random-access inspection of individual nodes and explicit constant-to-declaration navigation.

## Build from pinned export

**Verify the compressed download checksum before decompressing**. The published original export's SHA-256 expected by the existing workflow is `61a8938ad5f5e57397c1c0e3b954916af546d9004ade01c3555744a681b05381`.

```bash
sha256sum solution.ndjson.zst
zstd -d --long=30 -c solution.ndjson.zst | \
  python3 tools/rh_graph_explorer.py build \
    --output-dir analysis/expr-viewer \
    --compressed-sha256 61a8938ad5f5e57397c1c0e3b954916af546d9004ade01c3555744a681b05381
python3 tools/rh_graph_explorer.py serve --index-dir analysis/expr-viewer
# Open http://127.0.0.1:8765/
```

The `--compressed-sha256` flag is **provenance metadata only**, not a verification action. Verify the download independently (`sha256sum -c`) before invoking the command. The index independently calculates the SHA-256 of the decompressed NDJSON bytes it actually processed.

The builder writes a SQLite indexed name/declaration catalog and independently compressed expression blocks, plus a packed expression-to-block-location table. Each expression can be expanded by reading one compressed block (typically 1 MiB uncompressed); the viewer never preloads the complete proof. It is lossless with respect to exported expression and declaration JSON, including binders, universes, literals, projections, and shared expression IDs. The builder validates expression ordering, references, declarations, and root presence, and publishes no index on an input error.

The builder needs scratch disk for the compressed blocks and SQLite database. This representation is optimized for local random access, not for a single static HTML asset or for GitHub Pages. For multi-gigabyte corpora use sufficient storage and avoid uploading the index as a routine CI artifact. For a small test, use the official `Nat.add_succ` sample with `--root Nat.add_succ`.

```bash
python3 -m unittest discover -s tools -p test_rh_graph_explorer.py -v
```

## Evidence boundary

The indexed export represents the **original published proof** at the externally supplied export hash, not automatically the modified fork. Parsing a valid official exporter stream and displaying expressions does not independently replay Lean's kernel, prove that the modified Lean source compiles, or establish which declarations can be deleted. The original exact-graph five-root closure analyzer remains a separate gate: this viewer does not claim to calculate its five-root dependency membership counts.

To advance to a true *source AST* browser, separately export source syntax spans with an instrumented Lean frontend, bind those spans to checked declarations, and distinguish the source/elaboration mapping from the kernel-expression graph. Never infer source-to-proof attribution solely from file paths or identifier strings.