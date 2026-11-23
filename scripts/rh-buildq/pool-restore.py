#!/usr/bin/env python3
"""rh-buildq pool restore: register every known input-hash -> artifact mapping with Lake.

usage: pool-restore.py <project-dir> [extra-revision ...]

Collects (public, no credentials):
  rh-buildq/pool/<tc>.jsonl              union of everything rh-buildq publishers uploaded
  rh-buildq/maps/<HEAD>.jsonl            this commit's own partial publication (if any)
  revisions/<repo>/tc/<tc>/<sha>.jsonl   stock Lake maps for HEAD, its parents, and extra revisions
                                          (e.g. maps published for a PR head or GitHub's merge commit)
merges them into .lake/rh-buildq-pool.jsonl, runs `lake cache add` on it and downloads the
artifacts missing locally.  Lake then restores a module exactly when the module's own input
hash is in the map; anything else is compiled.

Environment (all optional, set from job.env by run-build.sh):
  MAP_PREFIX       key prefix for the pool and maps (default rh-buildq; tests use their own)
  MAP_NAME         this build's own map is <prefix>/maps/<MAP_NAME>.jsonl (default HEAD)
  POOL_EXTRA_MAPS  space-separated further map keys to merge, e.g. the per-chunk maps of the
                   rh-shard chunks this build requires
"""
import json, os, subprocess, sys, time, urllib.error, urllib.request
from pathlib import Path

PUBLIC = "https://rh-cache.taucetiproject.org/"
REPO = "leanprover-community/riemann-hypothesis"
SCHEMA = "2026-03-17"


def fetch(key):
    """GET a public key; None on 404. Retries CDN 5xx and transport errors."""
    req = urllib.request.Request(PUBLIC + key, headers={"User-Agent": "rh-buildq/1", "Cache-Control": "no-cache"})
    for attempt in range(6):
        try:
            with urllib.request.urlopen(req, timeout=120) as r:
                return r.read()
        except urllib.error.HTTPError as e:
            if e.code == 404:
                return None
            if e.code < 500 or attempt == 5:
                raise
        except (urllib.error.URLError, TimeoutError, ConnectionError):
            if attempt == 5:
                raise
        time.sleep(5 * 2 ** attempt)


def main():
    P = Path(sys.argv[1]).resolve()
    extra = sys.argv[2:]
    tc = (P / "lean-toolchain").read_text().strip()
    tcdir = tc.replace("/", "--").replace(":", "---")
    git = lambda *a: subprocess.check_output(["git", "-C", str(P), *a], text=True).split()
    head = git("rev-parse", "HEAD")[0]
    revs = git("rev-list", "--parents", "-n", "1", "HEAD") + extra
    prefix = os.environ.get("MAP_PREFIX") or "rh-buildq"
    keys = [f"{prefix}/pool/{tcdir}.jsonl", f"{prefix}/maps/{head}.jsonl"]
    if os.environ.get("MAP_NAME"):
        keys.append(f"{prefix}/maps/{os.environ['MAP_NAME']}.jsonl")
    keys += os.environ.get("POOL_EXTRA_MAPS", "").split()
    keys += [f"revisions/{REPO}/tc/{tcdir}/{r}.jsonl" for r in dict.fromkeys(revs)]
    merged = {}
    for key in keys:
        data = fetch(key)
        if not data:
            print(f"pool-restore: {key}: none")
            continue
        lines = data.decode().splitlines()
        if not lines or json.loads(lines[0]) != SCHEMA:
            print(f"pool-restore: {key}: unexpected schema, skipped")
            continue
        n = 0
        for l in lines[1:]:
            if l:
                k, v = json.loads(l)
                if k not in merged:
                    merged[k] = v; n += 1
        print(f"pool-restore: {key}: {len(lines) - 1} entries ({n} new)")
    out = P / ".lake/rh-buildq-pool.jsonl"
    out.write_text(json.dumps(SCHEMA) + "\n" + "".join(json.dumps([k, v]) + "\n" for k, v in sorted(merged.items())))
    print(f"pool-restore: registering {len(merged)} mappings")
    if merged:
        env = dict(os.environ, LAKE_CACHE_DIR=str(P / ".lake/cache"))
        subprocess.run(["lake", "cache", "add", str(out)], cwd=P, env=env, check=True)
        # Lake 4.37 does not fetch artifacts lazily during `lake build`; prefetch the missing ones.
        # Each pass downloads only what is still missing, so repeating it recovers from CDN errors.
        for _ in range(3):
            r = subprocess.run([sys.executable, "-I", str(Path(__file__).with_name("fetch-artifacts.py")), str(out),
                                str(P / ".lake/cache")])
            if r.returncode == 0:
                break


if __name__ == "__main__":
    main()
