# Community RH CI integrated into the fork

This fork pins the actual
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
Git repository at commit
[`79c751e0b0a5ea3bbfc20198c852fa85f28661e6`](https://github.com/leanprover-community/riemann-hypothesis/commit/79c751e0b0a5ea3bbfc20198c852fa85f28661e6)
as the submodule `upstream/riemann-hypothesis-community`.

Update or inspect the original sources and scripts with:

```bash
git submodule update --init upstream/riemann-hypothesis-community
git -C upstream/riemann-hypothesis-community rev-parse HEAD
```

No upstream scripts are maintained independently here. The
[`rh-community-upstream.yml`](.github/workflows/rh-community-upstream.yml)
workflow checks out exactly the pinned community revision, checks that the fork
uses the same Lean toolchain and Mathlib manifest, and runs the **upstream**
preparation, publisher-trust and runner tests. The manually dispatched large
build calls upstream `scripts/ci-prepare.py prepare` and `scripts/ci-build.py`
unchanged against the fork's committed source snapshot.

## Running the full build

The full build is disabled for automatic PR events. It requires an isolated
self-hosted Linux runner labeled `rh-build`, with Bubblewrap, a working
`systemd --user`, elan/Lean, substantial CPU/RAM and persistent disk.
The community's [runner guidance](https://github.com/leanprover-community/riemann-hypothesis/blob/79c751e0b0a5ea3bbfc20198c852fa85f28661e6/verification/CI-RUNNERS.md)
recommends approximately 128 GiB RAM and at least 250 GiB free SSD.

From GitHub Actions on the default branch, dispatch **RH community upstream
build infrastructure** for the desired trusted commit. The full-build job
uses upstream's SHA-256-verified original baseline cache, source sandbox,
resource limits, completed-work checkpoints and stock Lake recovery. It
uploads only small evidence files; it does **not** republish untrusted build
archives or use the community publisher's Cloudflare credentials.

The fork's `tools/rh_ci_identity.py` is a small source-only identity
adapter, not a second cache builder. It produces the fork-specific
`ci-prepare.py` request fields. The upstream scripts remain authoritative.

## Trust boundary

Community caches can include untrusted build outputs. Digest checks establish
artifact provenance, not proof correctness. A fresh source-derived build of
the five roots followed by exact theorem-type comparison, axiom closure review
and independent kernel checking is still required. A green CI integration
check or successful warm compilation does **not** establish those claims.

The manual full build has **not been executed on this fork** until an adequate
runner is available. The upstream publication workflow hard-codes the
community repository and is intentionally **not** invoked in this fork.
The submitted mathematical proof sources were released without an explicit
license. A submodule preserves the author's original source and history
rather than copying an independently maintained distribution.
