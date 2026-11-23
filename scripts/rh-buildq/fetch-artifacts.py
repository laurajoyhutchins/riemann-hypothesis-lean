#!/usr/bin/env python3
"""Download every artifact named in a Lake map that is missing from a local Lake cache.

usage: fetch-artifacts.py <map.jsonl> <cache-dir>
Stock Lake 4.37 does not download artifacts lazily during `lake build`: a mapped module whose
artifact is absent locally is simply compiled. So restores must prefetch. Files are written
to <cache-dir>/artifacts/<hash16>.ltar atomically. Objects are content-addressed and write-once
(If-None-Match) in R2.
"""
import json, os, subprocess, sys, tempfile
from pathlib import Path

PUBLIC = "https://rh-cache.taucetiproject.org/artifacts/leanprover-community/riemann-hypothesis/"
mapping, cache = Path(sys.argv[1]), Path(sys.argv[2]) / "artifacts"
cache.mkdir(parents=True, exist_ok=True)
lines = mapping.read_text().splitlines()[1:]
names = sorted({json.loads(l)[1] for l in lines if l})
missing = [n for n in names if not (cache / n).exists()]
print(f"fetch-artifacts: {len(names)} mapped, {len(missing)} missing locally", flush=True)
if missing:
    with tempfile.TemporaryDirectory(prefix="fetch-", dir=cache.parent) as t:
        conf = Path(t) / "curl.conf"
        conf.write_text("".join(f'url = "{PUBLIC}{n[:-5]}.art"\noutput = "{t}/{n}"\n' for n in missing))
        r = subprocess.run(["curl", "--disable", "--fail", "--silent", "--show-error", "--location", "--retry", "5",
                            "--retry-all-errors", "--parallel", "--parallel-max", "200", "--config", str(conf)])
        got = 0
        for n in missing:
            p = Path(t) / n
            if p.is_file() and p.stat().st_size:
                os.chmod(p, 0o444); os.replace(p, cache / n); got += 1
        print(f"fetch-artifacts: downloaded {got}/{len(missing)} (curl exit {r.returncode})", flush=True)
        sys.exit(0 if got == len(missing) else 1)
