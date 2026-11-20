# Five-theorem RH minimization experiment

Branch base: `7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.
Toolchain: `leanprover/lean4:v4.33.1`.
Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.
The original 175,187-file, 17,374,215-line source baseline is reported by
[Deicyde's independent audit](https://github.com/Deicyde/riemann-hypothesis/blob/main/verification/NOTES.md);
it has **not** been re-counted on this branch.

## Status

This is an **unverified import-boundary experiment** and a **not-yet-executed
Lean declaration census**. The five theorem declarations and proof bodies in
`src/Main.lean` have *not* changed. Only its import of
`Supplements.Kernels.MainTheoremsAll` was replaced with a direct import of
`Supplements.Kernels.MainTheorems`, where `allChi`, `rhOfAll`,
`critAll`, and `claimAll` are defined. This may permit later source deletion;
it saves **zero physical source lines by itself**.

No successful build of this branch, axiom comparison, independent kernel
replay, or source size reduction is claimed.

## Run the experiment on a machine with adequate RAM/disk

1. Check out the branch at the exact commit being tested.
2. Execute `lake exe cache get` and `lake build Main`.
3. Execute `lake env lean tools/RHDeclarationCensus.lean`.
4. Execute `python3 tools/enrich_census.py --src src --declarations analysis/rh-declaration-modules.tsv --out analysis`.
5. Execute `python3 -m unittest discover -s tools -p 'test_*.py' -v`.

Run those same commands with the *original* commit on a separate worktree and
keep the two sets of outputs. The census loads `Main`, so its process alone
may be prohibitively memory-intensive. A failed import, error, timeout,
OOM, or missing declaration is **not** a successful zero count.

Produced artifacts:

- `analysis/rh-targets.tsv`: target names, Lean expression representations
  of elaborated types, universe parameter lists, and transitive axiom names.
- `analysis/rh-declaration-modules.tsv`: declaration counts grouped by
  defining module, both expression-only and mutual-block-conservative closure.
- `analysis/rh-declaration-edges.tsv`: exact syntactic kernel-expression edges
  between checked constants, labeled `type`, `value`, `structural`, or
  `mutual-block`. This can identify direct users of a proposed wrapper alias;
  it does not capture tactic or syntax-level uses.
- `analysis/rh-module-lines.tsv`: each source module's physical line count
  and closure counts.
- `analysis/rh-line-census.json`: size and conservative deletion upper bounds.

The counting script counts byte-level physical lines, including any last
unterminated line. The counting boundary is `src/**/*.lean` exactly, as in the
original archive; tooling is reported separately, **not hidden or substituted
for proof files**. To compare a reduced development, include all *required*
proof source in its count, not just the `src` tree if code has moved elsewhere.

## Interpretation

The expression closure follows `ConstantInfo.getUsedConstantsAsSet` from
Lean v4.33.1, covering declaration types, theorem proof terms, definitions,
opaque values, and inductive/recursor relationships. The conservative closure
additionally retains whole mutual declaration blocks. Both are derived from
the *imported environment*, which means a proof-visible declaration can be
missing even from source-only syntax inspection.

These are **kernel-expression analyses**, not exact source-build closures.
They cannot see syntax extensions, tactic implementation dependencies,
macro elaboration, attributes, instances, coercions, or module initialization
that become unnecessary after elaboration. Some kernel rules, notably string
literal reduction and induction/quotient infrastructure, need additional
care before any executable kernel-only replay.

A module with zero block-reachable declarations is only a **candidate** for
whole-module deletion. Its line count is an upper bound on possible source
savings, **not** a verified saving. For a module with a mixture of reachable
and unreachable declarations, declarations alone do not provide source-line
spans, so no line savings are estimated.

The audit script explicitly reports `verified_prunable_lines: 0`. Raise
that only after deleting candidate source, clean-building all five statements,
comparing checked types/universes and axiom sets against the original and
obtaining independent kernel acceptance for the new tree.

## Root theorem preservation

The target names, including capitalization, are

`riemannHypothesis`,
`riemannZeta_eq_zero_re`,
`LFunction_ne_zero_of_half_lt_re`,
`LFunction_eq_zero_re`,
`LFunction_eq_zero_re_of_isPrimitive`.

Do not interpret type-expression *printing* as sufficient proof. Check
structural type expression equality with controlled environment imports and
a Comparator-style independent challenge. In addition to `lake build Main`,
perform a source-bound proof export and replay by the hardened Lean kernel and
an independent checker such as `nanoda`.

## Scaffolding case

`ActMemMK.lean` proves `GlobalTheory.TieMK.act_mem_MK_alt`.
`ActMemMKStatement.lean` declares
`GlobalTheory.T.rho_mem_MK_of_mem_MK` using that proof and an equivalent
formula, but may have consumers. Its apparent redundancy was verified by
*textual source inspection only*. Search all checked constants referencing
the wrapper and all source elaboration consumers before redirecting and
removing it. No alias has yet been removed.

## Limits

- The import-boundary change has not passed Lean. Do not merge it as a
  verified mathematical refactor.
- No declaration closure count or feasible pruning bound has been produced.
- A full reproducing build is large, and an earlier independent report used
  hundreds of GiB of RAM.
- The author's published archive did not state an explicit redistribution
  license. Preserve attribution and settle reuse permissions before broader
  redistribution of a modified source tree.
