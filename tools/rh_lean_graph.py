#!/usr/bin/env python3
"""Generate an RH driver using *upstream* Lean Graph, without forking its code.

Run the generated file with `lake env lean analysis/RHLeanGraph.lean` after
`lake build Main`. The graph JSON files are written in the working directory.
"""
from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import re
import urllib.request

UPSTREAM_COMMIT = "12fe82c12a41a827265bac725351cade3511d28a"
EXTRACTOR_BLOB_SHA = "2cb37f37f01427086d2bf53a6fc8bdf4a8daaa69"
EXTRACTOR_URL = (
    "https://raw.githubusercontent.com/patrik-cihal/lean-graph/"
    + UPSTREAM_COMMIT + "/static/DependencyExtractor.lean"
)
RH_ROOTS = (
    "riemannHypothesis",
    "riemannZeta_eq_zero_re",
    "LFunction_ne_zero_of_half_lt_re",
    "LFunction_eq_zero_re",
    "LFunction_eq_zero_re_of_isPrimitive",
)
NAME_PATTERN = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*")


def git_blob_sha(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def verify_extractor(data: bytes) -> str:
    if git_blob_sha(data) != EXTRACTOR_BLOB_SHA:
        raise ValueError("upstream Lean Graph extractor differs from pinned Git blob")
    return data.decode("utf-8")


def generate_driver(extractor: str, roots: tuple[str, ...], depth: int) -> str:
    if depth < 1:
        raise ValueError("depth must be >= 1")
    if not roots or len(roots) != len(set(roots)):
        raise ValueError("select at least one distinct root")
    for root in roots:
        if not NAME_PATTERN.fullmatch(root):
            raise ValueError(f"invalid Lean constant name: {root!r}")
    header = (
        "/- RH visualization using the pinned upstream Lean Graph extractor.\n"
        "   See https://github.com/patrik-cihal/lean-graph\n"
        "   This is a depth-bounded declaration graph, not the full proof AST. -/\n"
        "import Main\n"
    )
    commands = "\n".join(
        f"#eval serializeAndWriteToFile (Source.Constant `(@{root})) {depth}"
        for root in roots
    )
    return header + extractor.rstrip() + "\n\n" + commands + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("analysis/RHLeanGraph.lean"))
    parser.add_argument("--depth", type=int, default=2,
                        help="upstream BFS depth, not an assertion of complete closure")
    parser.add_argument("--root", action="append",
                        help="Lean constant; repeat to override the default five final theorems")
    parser.add_argument("--extractor", type=Path,
                        help="offline upstream extractor file; checked against pinned Git blob")
    args = parser.parse_args()
    if args.extractor:
        data = args.extractor.read_bytes()
    else:
        request = urllib.request.Request(EXTRACTOR_URL, headers={"User-Agent": "RHLeanGraph/1"})
        with urllib.request.urlopen(request, timeout=60) as response:
            data = response.read()
    extractor = verify_extractor(data)
    roots = tuple(args.root) if args.root else RH_ROOTS
    source = generate_driver(extractor, roots, args.depth)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(source, encoding="utf-8")
    print(f"Wrote {args.output} ({len(roots)} root(s), depth {args.depth})")
    print("Run: lake build Main && lake env lean " + str(args.output))
    print("Then open each <theorem>.json in https://patrik-cihal.github.io/lean-graph/")


if __name__ == "__main__":
    main()
