# Experiment 001: minimal final-theorem entry point

**State:** implemented as a separate Lean target and conservative local-import analyzer; **not yet compiled or kernel-checked**. No theorem or existing proof has been deleted or replaced.

## Hypothesis

The original `src/Main.lean` imports `Supplements.Kernels.MainTheoremsAll`, whose immediate upstream modules add several small-class-number imports. Yet the five final theorem declarations visibly reference witnesses already defined in `Supplements.Kernels.MainTheorems`.

**Question:** can a root importing `Statements` and `Supplements.Kernels.MainTheorems` produce the same five proposition types and witnesses with a smaller import closure and/or lower build cost?

The answer is **unknown** until the tools below run on a complete checkout.

## Experimental artifacts

- [`src/MainMinimal.lean`](../src/MainMinimal.lean): same five declared proposition types and proof witnesses under `_minimal` names.
- [`lakefile.toml`](../lakefile.toml): adds nondefault `MainMinimal` Lean library root. The existing default-target list and `Main` root are left unchanged.
- [`tools/proof_import_graph.py`](../tools/proof_import_graph.py): standard-library-only source import graph analyzer. This is **not** a Lean elaborated-constant or theorem-dependency analyzer.
- [`tests/test_proof_import_graph.py`](../tests/test_proof_import_graph.py): fixture tests for nested comments, missing roots, unknown imports, and import-closure comparisons.
- [`checks/MainMinimalAudit.lean`](../checks/MainMinimalAudit.lean): Lean source to display the ten declaration types and axiom dependencies.

## Run reproducibly

Use a complete checkout at the exact candidate commit. Preserve command output, exit status, commit SHA, runner OS/CPU/RAM, Lean version, and duration/peak RSS.

```bash
git rev-parse HEAD
cat lean-toolchain
python3 -m unittest discover -s tests -v

# Conservative, local source-module reachability only:
python3 tools/proof_import_graph.py src \
  --root Main --root MainMinimal \
  --output docs/generated/import-summary.json \
  --graph-json docs/generated/module-graph.json

# Pinned Lake cache and build. These are potentially expensive:
lake exe cache get
lake build Statements
lake build MainMinimal
lake build Main

# Types and axiom inspection for both sets of declarations:
lake env lean checks/MainMinimalAudit.lean
```

The script treats known external module roots separately and fails closed on unknown imports, unreadable files, or missing roots. Provide any additional verified external package prefixes with repeated `--external-root`; do not mark an unresolved module as external just to obtain a favorable result.

**Suggested measurements:** elapsed seconds and peak RSS per command; local import-closure files/lines for `Main` vs `MainMinimal`; difference module names; total repository Lean lines; changes in `.olean` count/size if available. The import graph's `only_left_lines` is **not** a verified removal count.

## Accept or reject

1. **Source reachability:** if the import comparison shows no reduction, the hypothesis of a smaller module closure is false at the import level. Keep this negative result.
2. **Compilation:** if `MainMinimal` does not build, keep its exact error and first missing dependency. Do not patch proofs by introducing axioms.
3. **Statements and axiom audit:** compare all five elaborated types and emitted axiom sets; their expected types are textually identical to the original root's declarations, but this is not a substitute for Lean elaboration.
4. **Kernel evidence:** independently replay the exact candidate environment with a checker compatible with Lean 4.33.1. Document limitations and additional trust assumptions.
5. **Cost:** a smaller `Main` closure or faster targeted build is a useful CI result even if the full repository line count is unchanged. Remove physical source files only after checking all required targets and transitive dependencies.

No proof-preserving deletion is authorized by source reachability alone.

## Current observations

- The baseline target's import chain is `Main` → `MainTheoremsAll` → `MainTheoremsCritical` → `MainTheorems`.
- `MainTheoremsCritical` adds three small-class-number imports; `MainTheoremsAll` adds `CorGKOf`. Those imports may share transitive dependencies with the literature bridge, so their *net contribution to the closure is unknown*.
- Five unit tests for the analyzer passed against small synthetic fixtures in an isolated local Python runtime. These fixtures are not the RH checkout.

## Next step after the experiment

Extract elaborated constant-dependency closures for `UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin` and the five final theorems. This is a separate Lean-aware tool, not an extension of lexical import counting. See [research plan](proof-research-plan.md).
