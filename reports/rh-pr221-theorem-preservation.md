# RH PR #221: five-root preservation and independent verification audit

Status: **source integration proved by Git history and source census, kernel verification not yet performed.** This report describes evidence, not a certificate for the five final RH/Dirichlet claims.

## Pinned source snapshots

- Fork original main: `27dd5120b4ec31d32e8804b9cb4329caf0966a99`
- Community pre-compression: `97ed34c57bc0d159b51c77a9e7e2ba59932b1256`
- Community PR #221 merge: `98cc3736f046abae883d8cda839c84f3004257a7`
- Fork pre-PR sync: `b98d11cae860c084b6831bd7e34a847010643aa0`
- Fork source compression: `813e47dc1ccf86284e12f37b601f8130f20a984c`
- Fork community CI repin: `442c7fde89d3fd285c576715375695fbdcfc1ae6`

## Five final source declarations

All five are top-level declarations in `src/Main.lean`. Their *written expected propositions* are:

| Final theorem | Propositional type name | Before original fork | Pre/post PR #221 |
| --- | --- | --- | --- |
| `riemannHypothesis` | `RiemannHypothesis` | Present | Present |
| `riemannZeta_eq_zero_re` | `RiemannZetaZerosOnLine` | Present | Present |
| `LFunction_ne_zero_of_half_lt_re` | `DirichletLNonvanishingRightOfHalf` | Present | Present |
| `LFunction_eq_zero_re` | `DirichletLZerosOnLine` | Present | Present |
| `LFunction_eq_zero_re_of_isPrimitive` | `PrimitiveDirichletLZerosOnLine` | Present | Present |

The upstream PR #221 source edit did **not** touch `src/Main.lean` or `src/Statements.lean`. Both files have identical Git blob IDs in upstream's parent and merge commit:

- `src/Main.lean`: `67c65badc15f80a1db65df1c84dc7a4928fc410f`
- `src/Statements.lean`: `23b01f745b80075e377c415abae96ece3570d0b0`

Census SHA256 (file contents) before and after PR #221:

- `src/Main.lean`: `8747f40b178740867ed8aa53b5a6f6f32a23b7b8bc4fcbca898fe72fbf0fcdf6`
- `src/Statements.lean`: `3ab58a3af2384def08e6f71531c33939a83a1408e31ac5b0e75bf4afa488a463`

**Caution:** Both files differ from those in the original fork's source archive. The upstream pre-221 sync also updated Mathlib and the Lean source imports, so the source names in the table are **not** proof of identical *elaborated* theorem types across fork main and this branch. Similarly, source equality across PR #221 does not prove axiom or proof dependency equivalence.

## Verification matrix

| Obligation | Status | Evidence or blocker |
| --- | --- | --- |
| Complete PR #221 source patch | **PASS** | [Integration run 45215574639](https://github.com/laurajoyhutchins/riemann-hypothesis-lean/actions/runs/45215574639), full 3,369 changed paths and zero conflicts |
| Reproducible source census | **PASS** | `reports/rh-pr221-integration.json`, census unit self-test passed |
| PR #221 entrypoint source equality | **PASS** | Git blob and SHA256 pairs above |
| Syntactic newly introduced `sorry`/`admit`/`axiom` scan | **PASS with limited scope** | Added patch lines only; not a global proof-gap audit |
| Matching upstream Lake manifest/toolchain | **PASS, configuration only** | Fork Git blob IDs equal upstream post-#221 |
| Five fully elaborated theorem types: original fork vs synced fork | **NOT CHECKED** | Requires baseline/candidate Lean environments and normalized elaborated expression comparison |
| Five proof values independently checked by Lean kernel | **NOT CHECKED** | No full clean source reconstruction of this branch |
| Axiom dependencies and new assumptions | **NOT CHECKED** | Requires kernel-level constant/proof export or axiom audit on both builds |
| Proof-bearing declaration and exact reachable DAG delta | **NOT CHECKED** | Requires export / graph census on both checked environments |
| Clean build time and peak RSS | **NOT CHECKED** | Full build not executed |
| Community CI controller fast contract check | **NOT PASSED** | Initial PR-side workflow returned `action_required`, requiring workflow approval/execution |

## Reproducible source checks

```bash
git checkout research/upstream-pr221-integration-20261123
python3 tools/rh_pr221_census.py --test
python3 tools/rh_pr221_census.py
cat reports/rh-pr221-integration.json
git diff --numstat b98d11cae860c084b6831bd7e34a847010643aa0 813e47dc1ccf86284e12f37b601f8130f20a984c -- src
git rev-parse 813e47dc1ccf86284e12f37b601f8130f20a984c:src/Main.lean
git rev-parse b98d11cae860c084b6831bd7e34a847010643aa0:src/Main.lean
```

## Required independent verification before merge

Use the community-supplied pinned build controller already referenced in `.github/workflows/rh-community-upstream.yml`; do not mistake cached checks for clean proof verification. Independently reconstruct the fork base and post-PR states from source with pinned toolchains, export all five theorem types and proof dependencies from checked environments, compare normalized elaborated expressions modulo explicit universe-parameter renaming and alpha equivalence, audit all axioms, and record the run IDs and peak resource costs. Require a clean rebuilding of affected proofs and a kernel check of every final theorem. Keep PR in draft until these gates pass.

## Compression research direction

Upstream #221 proves that existing cohomological and inverse-function lemmas can replace duplicated tactic derivations. The largest historical source concentration in this fork is `Development/AbelianVarietyTheory/Proofs`, but no measurable transfer rate has been established. A selective, kernel-verified backport onto the **smaller original fork baseline** is preferable for the absolute under-10-million-line goal: upstream #221 saves 221,158 lines on its own baseline, while preceding upstream synchronization adds 3,414,684 lines compared to our smaller fork. Future candidate savings are unquantified.

See [technical notebook study](https://github.com/laurajoyhutchins/technical-notebook/blob/main/content/studies/upstream-rh-proof-reuse-compression.md).
