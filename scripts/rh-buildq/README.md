# Fragment builds against the shared cache

The `fragment` mode of `.github/workflows/build-pr.yml` builds a list of Lake targets of one
commit on a chosen self-hosted runner of the RiemannHypothesisBuild group. Finished modules are
published to the R2 cache while the build is still running. Chunks of an `rh-shard` plan can
then be built on several machines, and each machine picks up what the others have already
published. Dispatch it from `main`:

    gh workflow run build-pr.yml --ref main -f mode=fragment -f pr_number=0 \
      -f fragment_commit=<sha> -f fragment_targets='Mod.A Mod.B' -f fragment_runner=<label>

- `fragment_commit` is a SHA on GitHub, or `SHA BASE HEAD DATE PR` for the deterministic
  merge commit that `rh-buildq start <PR>` builds. The job recreates that merge and checks
  that it gets SHA.
- `fragment_targets` is a list of module names, `gz:<base64 of a gzipped list>`, an
  `https://` URL, or `git:<ref>:<path>` in this repository. For a URL or `git:` spec that
  points at an `rh-shard-plan/1` plan, append `#<chunk id>`. The job then builds that chunk's
  `targets`.
- `fragment_jobs` sets `LEAN_NUM_THREADS` (default: all cores).

Each job runs these steps:

1. `fragment.py restore` keeps one tree per run, in `$RH_FRAGMENT_ROOT/<sha>-<run id>/`
   (default `~/rh-fragments`). Rerunning the job reuses it. The tree of a successful run is
   deleted at the end. Each job also deletes the trees of other runs that have completed
   (with any conclusion); it keeps those of queued or running runs. When it cannot read a
   run's status, it deletes the tree only after a week untouched. The first
   time, it clones the repository and runs `lake exe cache get` at
   the nearest first-parent ancestor that has a published CI record. On every run it then
   merges the public maps (`pool-restore.py`: the `rh-buildq/pool` union, this commit's
   `rh-buildq/maps` entry and the stock revision maps), runs `lake cache add`, and prefetches
   missing artifacts (`fetch-artifacts.py`). Lake 4.37 compiles a mapped module whose artifact
   is not local; it does not download it.
2. `fragment.py build` runs `lake build -v -o outputs-<run>.jsonl <targets>` with
   `LAKE_RESTORE_ARTIFACTS=true`. With `-v`, Lake logs every module as Built or Replayed,
   not only those with messages. The job log shows compiled modules, failures and one
   progress line a minute; the full log is in the result artifact. `publish.py` runs alongside it and uploads settled modules
   every minute, as content-addressed `artifacts/...` objects. It records them in the
   `rh-buildq/maps/<sha>.jsonl` and `rh-buildq/pool/<toolchain>.jsonl` maps, which it updates
   by compare-and-swap.
3. `fragment.py flush` makes a final publication pass. It runs even when the build failed or
   the job was cancelled. After an interruption, it skips files from the last minute.
4. `fragment.py result` writes `result.json`: the built, replayed and failed modules, the
   publication counters, the outputs not yet in the cache, and the timings. The job uploads it
   as the artifact `fragment-result-<run>-<attempt>`, together with the gzipped build log.

Rerunning a job resumes the work: Lake replays everything already built in the tree. The
publisher skips input hashes it has already published or that it restored from.

The R2 keys are derived from `R2_ACCOUNT_TOKEN` (environment `ci-cache-publish`, which deploys
from `main` only). This happens after the restore, which runs the target's lakefile outside
any sandbox. The keys are written to `$RUNNER_TEMP`, and the publisher reads them from there.
When unprivileged bubblewrap works on the host, the build runs in a PID namespace where that
directory is an empty tmpfs. `result.json` records the outcome as `"sandbox": "bwrap"` or
`"none"`.

These files are copies of the rh-buildq host scripts. The only additions are retries on CDN
errors, the toolchain read from the project, no EC2 Spot probing off EC2, and `--settle` and
`--before` options for the publisher.
