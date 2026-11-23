#!/usr/bin/env python3
"""Build a fragment (a list of Lake targets) of one commit against the shared R2 cache.

Used by the `fragment` mode of .github/workflows/build-pr.yml; runs on any Linux host with
git, curl, python3 and elan. See README.md in this directory.

  fragment.py targets SPEC --out FILE
  fragment.py credentials --out FILE                 (reads $R2_ACCOUNT_TOKEN)
  fragment.py restore --queue Q --commit SPEC [--timings FILE]
  fragment.py build --queue Q --targets FILE --log LOG [--jobs N] [--creds FILE] [--hide DIR]...
  fragment.py flush --queue Q --creds FILE
  fragment.py result --queue Q --targets FILE --log LOG --out FILE [--timings FILE]
  fragment.py prune --root DIR                       (reads $GH_TOKEN, $GITHUB_RUN_ID)

The queue directory Q (one per workflow run) persists across reruns: it holds project/ (the
Lake workspace), job.env, phase, publish-state.json and known-maps/. A rerun restores the pool
again (other fragments may have published since) and lets Lake continue where it stopped.
"""
import argparse, base64, gzip, hashlib, json, os, re, resource, shutil, signal, subprocess, sys, time
import urllib.error, urllib.request
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO_URL = "https://github.com/leanprover-community/riemann-hypothesis"
PUBLIC = "https://rh-cache.taucetiproject.org/"
ACCOUNT = "ec2169bdf033f56b009956d4b64ba8ef"
SHA = re.compile(r"[0-9a-f]{40}\Z")
# Lean names may use any Unicode letter or subscript. Targets go to argv, never to a shell;
# a leading '-' would be read as a Lake option.
MODULE = re.compile(r"[^\s\-#+@:][^\s]*\Z")
MERGE_IDENTITY = {"GIT_AUTHOR_NAME": "rh-buildq", "GIT_AUTHOR_EMAIL": "rh-buildq@localhost",
                  "GIT_COMMITTER_NAME": "rh-buildq", "GIT_COMMITTER_EMAIL": "rh-buildq@localhost"}
PUBLISH_WAIT = 45 * 60
# A Lake job line, e.g. "✔ [12/40] Built Foo.Bar (2.1s)"; the mark is ✔, ⚠, ℹ or ✖ (failed).
LINE = re.compile(r"^\s*([✔⚠✖ℹ])\s+\[\d+/\d+\]\s+(Built|Replayed|Building|Ran|Running|Fetched|Fetching)\s+(\S+)")


def log(msg):
    print(f"=== [{time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}] {msg}", flush=True)


def http_get(url, tries=6):
    """GET with retries on 5xx and transport errors; None on 404."""
    req = urllib.request.Request(url, headers={"User-Agent": "rh-buildq-fragment/1", "Cache-Control": "no-cache"})
    for attempt in range(tries):
        try:
            with urllib.request.urlopen(req, timeout=120) as r:
                return r.read()
        except urllib.error.HTTPError as e:
            if e.code == 404:
                return None
            if e.code < 500 or attempt == tries - 1:
                raise
        except (urllib.error.URLError, TimeoutError, ConnectionError):
            if attempt == tries - 1:
                raise
        time.sleep(5 * 2 ** attempt)


def git(P, *args, env=None, capture=True):
    r = subprocess.run(["git", "-C", str(P), *args], check=True, text=True, env=env,
                       stdout=subprocess.PIPE if capture else None)
    return r.stdout.strip() if capture else ""


def phase(Q, name):
    tmp = Q / "phase.tmp"
    tmp.write_text(name + "\n")
    os.replace(tmp, Q / "phase")
    log(f"phase {name}")


def add_timing(path, key, seconds):
    if not path:
        return
    p = Path(path)
    data = json.loads(p.read_text()) if p.exists() else {}
    data[key] = round(seconds, 1)
    p.write_text(json.dumps(data, indent=1, sort_keys=True))


# --- targets -----------------------------------------------------------------------------------

def parse_targets(data, chunk):
    """A plan (rh-shard-plan/1, needs a chunk id) or a list of names (whitespace/comma separated)."""
    text = data.decode() if isinstance(data, bytes) else data
    if text.lstrip().startswith("{"):
        plan = json.loads(text)
        if plan.get("format") != "rh-shard-plan/1":
            raise SystemExit("targets: JSON is not an rh-shard-plan/1 plan")
        if not chunk:
            raise SystemExit("targets: a plan needs a chunk id (SPEC#R.A)")
        rows = [c for c in plan["chunks"] if c["id"] == chunk]
        if not rows:
            raise SystemExit(f"targets: no chunk {chunk} in the plan")
        names = rows[0]["targets"]
    else:
        if chunk:
            raise SystemExit("targets: #chunk only applies to a plan")
        names = [n for n in re.split(r"[\s,]+", text) if n and not n.startswith("#")]
    bad = [n for n in names if not MODULE.fullmatch(n)]
    if bad:
        raise SystemExit(f"targets: not module names: {bad[:5]}")
    if not names:
        raise SystemExit("targets: empty")
    return list(dict.fromkeys(names))


def cmd_targets(a):
    spec, chunk = a.spec.strip(), None
    if spec.startswith(("https://", "git:")) and "#" in spec:
        spec, chunk = spec.rsplit("#", 1)
    if spec.startswith("gz:"):
        data = gzip.decompress(base64.b64decode(spec[3:]))
    elif spec.startswith("https://"):
        data = http_get(spec)
        if data is None:
            raise SystemExit(f"targets: {spec}: 404")
    elif spec.startswith("git:"):
        # git:<ref>:<path>, read from the public repository without a full checkout.
        _, ref, path = spec.split(":", 2)
        tmp = Path(a.out).with_suffix(".git")
        if not tmp.exists():
            subprocess.run(["git", "init", "-q", "--bare", str(tmp)], check=True)
        subprocess.run(["git", "-C", str(tmp), "fetch", "-q", "--depth=1", "--filter=blob:none", REPO_URL, ref],
                       check=True)
        data = subprocess.run(["git", "-C", str(tmp), "show", f"FETCH_HEAD:{path}"], check=True,
                              stdout=subprocess.PIPE).stdout
        shutil.rmtree(tmp)
    else:
        data = spec
    names = parse_targets(data, chunk)
    Path(a.out).write_text("".join(n + "\n" for n in names))
    print(f"targets: {len(names)} targets")


# --- credentials ---------------------------------------------------------------------------------

def cmd_credentials(a):
    """Turn the Cloudflare account API token into R2 S3 keys (token id, sha256 of the token)."""
    token = os.environ.pop("R2_ACCOUNT_TOKEN", "")
    out = Path(a.out)
    if not token or any(c.isspace() for c in token):
        print("credentials: no R2_ACCOUNT_TOKEN; this job will build without publishing")
        return
    req = urllib.request.Request(f"https://api.cloudflare.com/client/v4/accounts/{ACCOUNT}/tokens/verify",
                                 headers={"Authorization": f"Bearer {token}"})
    with urllib.request.urlopen(req, timeout=30) as r:
        result = json.load(r)
    if not result.get("success") or result.get("result", {}).get("status") != "active":
        raise SystemExit("credentials: the account API token is not active")
    out.parent.mkdir(parents=True, exist_ok=True)
    os.chmod(out.parent, 0o700)
    fd = os.open(out, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
    with os.fdopen(fd, "w") as f:
        json.dump({"accessKeyId": result["result"]["id"],
                   "secretAccessKey": hashlib.sha256(token.encode()).hexdigest()}, f)
    print("credentials: R2 publisher keys ready")


# --- restore -------------------------------------------------------------------------------------

def restore_from(P, target):
    """Nearest first-parent ancestor (or the target itself) with a published CI record."""
    for rev in git(P, "rev-list", "--first-parent", "-n", "50", target).split():
        req = urllib.request.Request(f"{PUBLIC}ci/revisions/{rev}.json", method="HEAD",
                                     headers={"User-Agent": "rh-buildq-fragment/1"})
        try:
            with urllib.request.urlopen(req, timeout=60):
                return rev
        except urllib.error.HTTPError:
            continue
    raise SystemExit("restore: no ancestor within 50 first-parent commits has a published CI cache")


def cmd_restore(a):
    """SPEC is `SHA` (a commit on GitHub) or `SHA BASE HEAD DATE [PR]`: the deterministic merge
    of HEAD into BASE that `rh-buildq start <PR>` builds, which must have that SHA."""
    Q = Path(a.queue)
    parts = a.commit.split()
    target = parts[0]
    if not SHA.fullmatch(target) or len(parts) not in (1, 4, 5) or not all(SHA.fullmatch(p) for p in parts[1:3]):
        raise SystemExit("restore: --commit must be SHA or 'SHA BASE HEAD DATE [PR]'")
    Q.mkdir(parents=True, exist_ok=True)
    P = Q / "project"
    t0 = time.time()
    if not (P / ".git").is_dir():
        phase(Q, "clone")
        tmp = Q / "project.tmp"
        shutil.rmtree(tmp, ignore_errors=True)
        subprocess.run(["git", "clone", "-q", REPO_URL, str(tmp)], check=True)
        os.replace(tmp, P)
    extra = []
    if subprocess.run(["git", "-C", str(P), "cat-file", "-e", target + "^{commit}"],
                      stderr=subprocess.DEVNULL).returncode != 0:
        phase(Q, "fetch")
        if len(parts) == 1:
            git(P, "fetch", "-q", "origin", target, capture=False)
        else:
            base, head, date = parts[1:4]
            pr = parts[4] if len(parts) == 5 else None
            git(P, "fetch", "-q", "origin", base, head, capture=False)
            tree = git(P, "merge-tree", "--write-tree", base, head)
            msg = f"Merge PR {pr} ({head[:8]}) into main ({base[:8]})" if pr else f"Merge {head[:8]} into {base[:8]}"
            env = dict(os.environ, **MERGE_IDENTITY, GIT_AUTHOR_DATE=date, GIT_COMMITTER_DATE=date)
            sha = git(P, "commit-tree", tree, "-p", base, "-p", head, "-m", msg, env=env)
            if sha != target:
                raise SystemExit(f"restore: merge SHA mismatch: got {sha}, want {target}")
            git(P, "update-ref", f"refs/rh-buildq/{target}", sha)
    if len(parts) > 1:
        extra = [parts[2]]  # maps published for the PR head
    lean_tc = git(P, "show", f"{target}:lean-toolchain")
    tcdir = lean_tc.replace("/", "--").replace(":", "---")
    marker = Q / "restored-ancestor"
    if not marker.exists():
        src = restore_from(P, target)
        phase(Q, "restore-ancestor")
        log(f"restoring the complete CI cache of {src}")
        git(P, "checkout", "-q", "--detach", src, capture=False)
        for attempt in range(1, 5):
            if subprocess.run(["lake", "exe", "cache", "get"], cwd=P).returncode == 0:
                break
            log(f"cache get attempt {attempt} failed; retrying (downloaded artifacts are kept)")
            time.sleep(20)
        else:
            log("WARNING: ancestor cache restore incomplete; Lake will compile what is missing")
        marker.write_text(src + "\n")
    src = marker.read_text().strip()
    add_timing(a.timings, "restore_ancestor_s", time.time() - t0)
    t1 = time.time()
    if git(P, "rev-parse", "HEAD") != target:
        git(P, "checkout", "-q", "--detach", target, capture=False)
    (Q / "job.env").write_text(f"TARGET={target}\nRESTORE_FROM={src}\nTOOLCHAIN_DIR={tcdir}\n"
                               f"POOL_EXTRA_REVS=\"{' '.join(extra)}\"\n")
    # The pool grows while other fragments publish, so this runs on every job.
    phase(Q, "restore-pool")
    r = subprocess.run([sys.executable, "-I", str(HERE / "pool-restore.py"), str(P), *extra])
    if r.returncode != 0:
        log("pool restore failed (continuing; Lake will compile what is missing)")
    known = Q / "known-maps"
    known.mkdir(exist_ok=True)
    rec = http_get(f"{PUBLIC}ci/revisions/{src}.json")
    if rec:
        data = http_get(PUBLIC + json.loads(rec)["map_key"])
        if data:
            (known / "restore-from.jsonl").write_bytes(data)
    pool = P / ".lake/rh-buildq-pool.jsonl"
    if pool.exists():
        shutil.copyfile(pool, known / "pool-restore.jsonl")
    add_timing(a.timings, "restore_pool_s", time.time() - t1)
    phase(Q, "restored")


# --- build ---------------------------------------------------------------------------------------

def sandbox_prefix(hide):
    """bwrap command that hides the credential directories and the host's processes from Lean code
    run by the build, or [] where unprivileged bwrap is unavailable."""
    if not hide or not shutil.which("bwrap"):
        return []
    base = ["bwrap", "--dev-bind", "/", "/", "--proc", "/proc", "--unshare-pid", "--die-with-parent"]
    for d in hide:
        base += ["--tmpfs", d]
    if subprocess.run(base + ["true"], stderr=subprocess.DEVNULL).returncode != 0:
        return []
    return base + ["--"]


def raise_limits():
    """Soft limits as in run-build.sh: 65536 open files, unlimited (or the hard limit) stack."""
    for lim, want in ((resource.RLIMIT_NOFILE, 65536), (resource.RLIMIT_STACK, None)):
        _, hard = resource.getrlimit(lim)
        new = hard if want is None or (hard != resource.RLIM_INFINITY and hard < want) else want
        try:
            resource.setrlimit(lim, (new, hard))
        except (ValueError, OSError):
            pass


def start_publisher(Q, creds, hide):
    if not creds or not Path(creds).is_file():
        log("no publisher credentials: building without publishing")
        return None
    tmp = Path(hide[0]) / "publish-tmp" if hide else Q / "publish-tmp"
    tmp.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, RH_BUILDQ_CREDS=str(creds), TMPDIR=str(tmp))
    out = open(Q / "publish.log", "ab")
    log(f"publisher started; log {Q / 'publish.log'}")
    return subprocess.Popen([sys.executable, "-I", str(HERE / "publish.py"), str(Q), "--interval", "60"],
                            env=env, stdout=out, stderr=subprocess.STDOUT, start_new_session=True)


def cmd_build(a):
    Q = Path(a.queue).resolve()
    P = Q / "project"
    targets = Path(a.targets).read_text().split()
    jobs = a.jobs or os.cpu_count() or 1
    (Q / "interrupted-at").unlink(missing_ok=True)
    (Q / "exit-code").unlink(missing_ok=True)
    phase(Q, "build")
    publisher = start_publisher(Q, a.creds, a.hide)
    prefix = sandbox_prefix(a.hide)
    (Q / "sandbox").write_text("bwrap\n" if prefix else "none\n")
    log(f"lake build of {len(targets)} targets, LEAN_NUM_THREADS={jobs}, sandbox={'bwrap' if prefix else 'none'}")
    env = dict(os.environ, LAKE_CACHE_DIR=str(P / ".lake/cache"), LAKE_RESTORE_ARTIFACTS="true",
               LEAN_NUM_THREADS=str(jobs))
    env.pop("LAKE_ARTIFACT_CACHE", None)
    env.pop("R2_ACCOUNT_TOKEN", None)
    raise_limits()
    outputs = Q / f"outputs-{os.environ.get('GITHUB_RUN_ID', 'local')}.jsonl"
    t0 = time.time()
    # -v: Lake reports every job, so the log records each module as Built or Replayed. Without
    # it, modules that compile silently do not appear at all.
    proc = subprocess.Popen(prefix + ["lake", "build", "-v", "-o", str(outputs), *targets], cwd=P, env=env,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, start_new_session=True)

    def interrupted(signum, frame):
        (Q / "interrupted-at").write_text(f"{time.time()}\n")
        log(f"signal {signum}: stopping the build")
        live = [p for p in (proc, publisher) if p and p.poll() is None]
        for p in live:
            os.killpg(p.pid, signal.SIGTERM)
        # The flush step must not race a still-running Lake: wait, then kill what is left.
        for p in live:
            try:
                p.wait(20)
            except subprocess.TimeoutExpired:
                os.killpg(p.pid, signal.SIGKILL)
        phase(Q, "failed")
        sys.exit(128 + signum)

    signal.signal(signal.SIGTERM, interrupted)
    signal.signal(signal.SIGINT, interrupted)
    # The full log goes to the file; the job log gets compiled modules, failures and progress.
    last = 0.0
    with open(a.log, "ab") as logf:
        for line in proc.stdout:
            logf.write(line)
            text = line.decode(errors="replace")
            m = LINE.match(text)
            show = (m and (m[1] == "✖" or m[2] == "Built")) or text.startswith(("error", "Build ", "Some required"))
            if not show and m and time.time() - last > 60:
                show, last = True, time.time()
            if show:
                sys.stdout.write(text)
                sys.stdout.flush()
    code = proc.wait()
    signal.signal(signal.SIGTERM, signal.SIG_DFL)
    signal.signal(signal.SIGINT, signal.SIG_DFL)
    add_timing(a.timings, "build_s", time.time() - t0)
    (Q / "exit-code").write_text(f"{code}\n")
    phase(Q, "done" if code == 0 else "failed")
    if publisher:
        t1 = time.time()
        log("waiting for the publisher's final pass")
        try:
            publisher.wait(PUBLISH_WAIT)
        except subprocess.TimeoutExpired:
            log("publisher still running after the wait; stopping it (the flush step continues)")
            os.killpg(publisher.pid, signal.SIGTERM)
        add_timing(a.timings, "publish_tail_s", time.time() - t1)
    sys.exit(code)


def cmd_flush(a):
    """Final publication pass; runs even when the job failed or was cancelled."""
    Q = Path(a.queue).resolve()
    if not a.creds or not Path(a.creds).is_file() or not (Q / "job.env").exists():
        print("flush: nothing to publish (no credentials or no restored project)")
        return
    # If the build step was killed without its handler running, its Lake and publisher may still
    # be alive. They are matched by this run's queue path, which nothing else uses.
    for pattern in (f"-o {Q}/outputs-", f"publish.py {Q} "):
        if subprocess.run(["pkill", "-TERM", "-f", "--", pattern]).returncode == 0:
            log(f"stopped leftover processes matching {pattern!r}")
            if not (Q / "interrupted-at").exists():
                (Q / "interrupted-at").write_text(f"{time.time()}\n")
            time.sleep(10)
    if (Q / "phase").read_text().strip() not in ("done", "failed"):
        phase(Q, "failed")
    args = [sys.executable, "-I", str(HERE / "publish.py"), str(Q), "--once", "--settle", "0"]
    stop = Q / "interrupted-at"
    if stop.exists():
        args += ["--before", str(float(stop.read_text()) - 60)]
    env = dict(os.environ, RH_BUILDQ_CREDS=str(a.creds))
    if a.tmp:
        Path(a.tmp).mkdir(parents=True, exist_ok=True)
        env["TMPDIR"] = a.tmp
    t0 = time.time()
    subprocess.run(args, env=env, check=False)
    add_timing(a.timings, "flush_s", time.time() - t0)


# --- prune ---------------------------------------------------------------------------------------

TREE = re.compile(r"[0-9a-f]{40}-([0-9]+)\Z")
STALE_DAYS = 7


def run_status(run_id):
    """Workflow run status ("completed", "in_progress", ...) or None if it cannot be read."""
    token, repo = os.environ.get("GH_TOKEN"), os.environ.get("GITHUB_REPOSITORY")
    if not token or not repo:
        return None
    req = urllib.request.Request(f"https://api.github.com/repos/{repo}/actions/runs/{run_id}",
                                 headers={"Authorization": f"Bearer {token}", "Accept": "application/vnd.github+json",
                                          "User-Agent": "rh-buildq-fragment/1"})
    try:
        with urllib.request.urlopen(req, timeout=30) as r:
            return json.load(r).get("status")
    except (urllib.error.URLError, TimeoutError, ValueError):
        return None


def cmd_prune(a):
    """Delete other runs' trees once their run has completed (a rerun then restores afresh); keep
    trees of runs still queued or in progress. If the status is unreadable, fall back to age."""
    root, current = Path(a.root), os.environ.get("GITHUB_RUN_ID")
    for d in sorted(root.iterdir()) if root.is_dir() else []:
        m = TREE.fullmatch(d.name)
        if not m or not d.is_dir() or m[1] == current:
            continue
        status = run_status(m[1])
        old = time.time() - d.stat().st_mtime > STALE_DAYS * 86400
        if status == "completed" or (status is None and old):
            log(f"prune: removing {d} (run {m[1]}: {status or 'status unknown'}, {'stale' if old else 'recent'})")
            shutil.rmtree(d, ignore_errors=True)
        else:
            print(f"prune: keeping {d} (run {m[1]}: {status or 'status unknown'})")


# --- result --------------------------------------------------------------------------------------



def cmd_result(a):
    Q = Path(a.queue).resolve()
    built, replayed, failed = set(), set(), set()
    text = Path(a.log).read_text(errors="replace") if Path(a.log).exists() else ""
    tail = False
    for line in text.splitlines():
        m = LINE.match(line)
        if m:
            mark, verb, name = m.groups()
            if mark == "✖":
                failed.add(name)
            elif ":" in name:
                continue  # facet jobs (`Mod:c.o`, `Mod:irArts`), not modules
            elif verb == "Built":
                built.add(name)
            elif verb == "Replayed":
                replayed.add(name)
        if line.startswith("Some required targets logged failures") or line.startswith("Some required builds logged failures"):
            tail = True
        elif tail and line.startswith("- "):
            failed.add(line[2:].strip())
        elif tail and line.strip():
            tail = False
    state = json.loads((Q / "publish-state.json").read_text()) if (Q / "publish-state.json").exists() else {}
    env = {}
    if (Q / "job.env").exists():
        env = dict(l.split("=", 1) for l in (Q / "job.env").read_text().splitlines() if "=" in l)
    outputs = sorted(Q.glob(f"outputs-{os.environ.get('GITHUB_RUN_ID', 'local')}.jsonl"))
    unpublished = None
    if outputs and state:
        known = set(state.get("published", {}))
        for f in (Q / "known-maps").glob("*.jsonl"):
            known.update(json.loads(l)[0] for l in f.read_text().splitlines()[1:] if l)
        rows = [json.loads(l) for l in outputs[0].read_text().splitlines()[1:] if l]
        unpublished = sum(1 for r in rows if r[0] not in known)
    code = (Q / "exit-code").read_text().strip() if (Q / "exit-code").exists() else None
    timings = json.loads(Path(a.timings).read_text()) if a.timings and Path(a.timings).exists() else {}
    result = {
        "schema": 1, "commit": env.get("TARGET"), "restore_from": env.get("RESTORE_FROM"),
        "runner": os.environ.get("RUNNER_NAME"), "run_id": os.environ.get("GITHUB_RUN_ID"),
        "cpus": os.cpu_count(), "sandbox": (Q / "sandbox").read_text().strip() if (Q / "sandbox").exists() else None,
        "exit_code": int(code) if code not in (None, "") else None,
        "interrupted": (Q / "interrupted-at").exists(),
        "targets": Path(a.targets).read_text().split() if Path(a.targets).exists() else [],
        "built_count": len(built), "replayed_count": len(replayed), "failed_count": len(failed),
        "built": sorted(built), "failed": sorted(failed),
        "published_total": len(state.get("published", {})), "uploaded": state.get("uploaded"),
        "already_present": state.get("already_present"), "pool_size": state.get("pool_size"),
        "publish_errors": state.get("errors", [])[-5:],
        "outputs_not_in_cache": unpublished,
        "timings_s": timings,
    }
    Path(a.out).write_text(json.dumps(result, indent=1) + "\n")
    summary = {k: v for k, v in result.items() if k not in ("built", "targets")}
    summary["failed"] = summary["failed"][:50]
    print(json.dumps(summary, indent=1))
    if os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a") as s:
            s.write("```json\n" + json.dumps(summary, indent=1) + "\n```\n")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("targets"); s.add_argument("spec"); s.add_argument("--out", required=True)
    s = sub.add_parser("credentials"); s.add_argument("--out", required=True)
    s = sub.add_parser("restore"); s.add_argument("--queue", required=True); s.add_argument("--commit", required=True)
    s.add_argument("--timings")
    s = sub.add_parser("build"); s.add_argument("--queue", required=True); s.add_argument("--targets", required=True)
    s.add_argument("--log", required=True); s.add_argument("--jobs", type=int, default=0); s.add_argument("--creds")
    s.add_argument("--hide", action="append", default=[]); s.add_argument("--timings")
    s = sub.add_parser("flush"); s.add_argument("--queue", required=True); s.add_argument("--creds")
    s.add_argument("--tmp"); s.add_argument("--timings")
    s = sub.add_parser("prune"); s.add_argument("--root", required=True)
    s = sub.add_parser("result"); s.add_argument("--queue", required=True); s.add_argument("--targets", required=True)
    s.add_argument("--log", required=True); s.add_argument("--out", required=True); s.add_argument("--timings")
    a = ap.parse_args()
    {"targets": cmd_targets, "credentials": cmd_credentials, "restore": cmd_restore, "build": cmd_build,
     "flush": cmd_flush, "result": cmd_result, "prune": cmd_prune}[a.cmd](a)


if __name__ == "__main__":
    main()
