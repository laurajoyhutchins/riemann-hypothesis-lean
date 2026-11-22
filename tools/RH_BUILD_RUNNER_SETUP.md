# Dedicated RH full-build runner activation

This page is an **operator runbook**, not an enrollment script. It does not provision
machines, register runners, generate GitHub tokens or claim that a build succeeded.

## What is waiting

[Run 45045955381](https://github.com/laurajoyhutchins/riemann-hypothesis-lean/actions/runs/45045955381)
was initiated from exact branch commit
[`ac022cc34842c3c26e360d8fd6acc7792346c7b2`](https://github.com/laurajoyhutchins/riemann-hypothesis-lean/commit/ac022cc34842c3c26e360d8fd6acc7792346c7b2).
The hosted community CI contract passed. The actual RH full build is queued for
`[self-hosted, linux, x64, rh-build]`, with no assigned runner at the last observation.
**Do not dispatch another full build.** A runner with those labels can pick up the
existing job if it remains queued. GitHub may time out queued jobs; inspect the
live run first and use a deliberate fresh dispatch only after expiry.

The job calls the **unchanged, pinned** community `ci-prepare.py` and
`ci-build.py` under the existing source-isolation and durable checkpoint
workflow. On a **successful** full build, it attempts the five-root upstream
Lean Graph extraction and uploads validated graph or explicit failure evidence.
The default graph depth is 2: a neighborhood, **not** the full proof DAG.

## Security boundary: public repository

GitHub explicitly discourages non-ephemeral self-hosted runners for public
repositories because workflows can persistently compromise the host. Use a
**dedicated, disposable Linux VM**, not a personal workstation, a shared
development box or a machine holding credentials. Use a **non-root runner
account**, no cloud metadata credentials, no SSH deploy keys, no passwordless
sudo for the job account, and no access to other projects' disks or secrets.
The entire VM is potentially compromised during/after a run. Provision a
persistent *dedicated* work disk if retaining completed modules across
interruptions, but destroy/recreate the compute environment between trust
boundaries. Review the queued exact SHA before enabling the final job label.

For this branch, the self-hosted workload is reachable through the existing
`rh-community-upstream.yml` exact-message push condition and the explicitly
dispatched `rh-graph-retained-build.yml` workflow. Never broaden it to
`pull_request` without a separate security review. In the current community
workflow, fork-side `candidate/tools/rh_ci_identity.py` executes on the host
and `candidate/tools/rh_graph_postbuild.py` also executes on the host
*after* compilation: these must be treated as reviewed trusted code for
the exact queued source revision, **not** as universally safe for arbitrary PRs.

Sources:
- [GitHub: secure use of self-hosted runners](https://docs.github.com/en/actions/reference/security/secure-use)
- [GitHub: add self-hosted runners](https://docs.github.com/en/actions/how-tos/manage-runners/self-hosted-runners/add-runners)
- [Community RH: CI runner guidance](https://github.com/leanprover-community/riemann-hypothesis/blob/79c751e0b0a5ea3bbfc20198c852fa85f28661e6/verification/CI-RUNNERS.md)

## VM prerequisites

- 64-bit Linux x86-64. The pinned community guidance recommends **128 GiB
  RAM, at least 250 GiB free SSD**, and `vm.max_map_count >= 1048576`.
- The workflow defaults to a **96 GiB** systemd user-scope memory cap,
  **8 workers**, a **12 GiB** free-disk reserve, and 24 hours maximum.
  These are execution limits, not guarantees the proof will fit.
- Git, C compiler, Python **3.11+**, curl, Bubblewrap, Elan/Lean, GNU
  `time`, and a working systemd **user** manager. User namespaces must
  be available for Bubblewrap. Upstream preparation fetches its verified
  Mathlib and original proof-artifact caches, so outbound access and disk
  I/O matter.
- Keep `RH_CI_STATE_DIR` on a sufficiently large, dedicated persistent disk,
  **outside** the GitHub Actions disposable `_work` checkout. The default
  is `$HOME/.local/share/riemann-build-state` for the runner account.
  Persist it across *interruptions*, not across different untrusted tenants.

Example for a fresh supported Ubuntu VM, as an administrator (adapt to the
distribution and storage layout):

```bash
sudo apt-get update
sudo apt-get install -y git curl ca-certificates python3 python3-venv \
  build-essential bubblewrap unzip jq time
sudo useradd --create-home --shell /bin/bash rhbuild
sudo loginctl enable-linger rhbuild
sudo sysctl -w vm.max_map_count=1048576
printf 'vm.max_map_count = 1048576\n' | \
  sudo tee /etc/sysctl.d/99-rh-build.conf
```

Install Elan from its [maintained project](https://github.com/leanprover/elan)
**as `rhbuild`**, following its current verified installation guidance.
Do not copy a personal `~/.elan` or private GitHub authentication files.
For remote CI, ensure the service account's `PATH` includes
`$HOME/.elan/bin` and that `elan which lean` works after the toolchain
is installed.

## Preflight as the actual runner account

Run these in a login shell for `rhbuild` and **check each result**:

```bash
uname -s && uname -m
python3 -c 'import sys; assert sys.version_info >= (3, 11)'
for tool in git gcc python3 curl bwrap elan lake systemd-run systemctl; do
  command -v "$tool" || exit 1
done
grep '^MemTotal:' /proc/meminfo
df -h "$HOME"
sysctl -n vm.max_map_count
systemctl --user show-environment
systemd-run --user --scope --quiet --property=MemoryMax=96G -- /usr/bin/true
bwrap --die-with-parent --unshare-all --ro-bind / / --proc /proc \
  --dev /dev -- /usr/bin/true
```

Failures of `systemctl --user` or `bwrap` must be fixed *before* adding
`rh-build`. Verify those commands also work under the **GitHub runner service
account**, not just in an interactive administrator shell. The community
controller intentionally refuses when systemd user scopes or namespace
isolation cannot be established. Do not disable these guards to get a green
workflow.

## Register in two phases

1. In the fork go to **Settings → Actions → Runners → New self-hosted runner**.
   Choose Linux x64 and follow the **current GitHub-generated download and
   SHA-256 verification commands**. Do not use a stale hard-coded runner
   tarball URL.
2. Configure under the dedicated `rhbuild` user. Supply the registration
   token **only to the machine**, never in chat, an issue, a commit, a log,
   or an artifact. Configure the initial custom label **`rh-staging`**,
   **not `rh-build`**. The automatic default labels should include
   `self-hosted`, `Linux`, and `X64`.
3. Start the runner via GitHub's current `./run.sh` instructions or install
   the systemd service via the generated `svc.sh` as documented by
   [GitHub](https://docs.github.com/en/actions/how-tos/manage-runners/self-hosted-runners/configure-the-application).
   Check it appears **online** in the repository. Preflight the service
   environment, storage, and isolation. Only then add the custom `rh-build`
   label in **Settings → Actions → Runners**.
4. When `rh-build` is assigned, the already queued full-build job can start
   if it has not expired. Confirm the exact
   [run 45045955381](https://github.com/laurajoyhutchins/riemann-hypothesis-lean/actions/runs/45045955381)
   transitions to `in_progress` and captures a real assigned runner name.
   Watch its **community controller receipt** before interpreting results.

## Acceptance sequence

A green runner-registration UI is not a proof result. Record, in order:

1. Actual self-hosted job assignment and source/configuration checks.
2. Full community controller `build_exit_code=0`, its candidate/source-tree
   identity, and retained successful checkpoint. A resource refusal is
   *inconclusive*, not a mathematical rejection.
3. Five upstream graph JSON files and combined graph with validated
   hashes, explicit depth/frontier statistics and extraction time/RSS.
4. Independent full modified-source Lean kernel verification, theorem
   type/universe and axiom comparison. A successful cached build and a
   closed **emitted-reference** graph do not replace this gate.
5. A separately measured attempt to open useful bounded graph neighborhoods
   in the upstream Lean Graph viewer. Full-graph interactive performance
   remains an independent scaling question.

The [technical notebook](https://github.com/laurajoyhutchins/technical-notebook/blob/main/content/studies/rh-lazy-kernel-expression-explorer.md)
keeps the proof/extraction trust boundaries and observed evidence distinct.
