#!/usr/bin/env python3
"""Read-only build-input identity compatible with the community RH CI schema.

No artifact is restored, trusted, published, or proof-checked by this script.
This copies only the *identity field convention*, not the community's cache
service, runner, publisher, or proof-verification machinery.

Reference: leanprover-community/riemann-hypothesis scripts/ci-prepare.py,
pinned investigation revision 8ec38f92ac54b5c91bc07f4f6f88ea61691b7975.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

INPUTS = ("lakefile.toml", "lake-manifest.json", "lean-toolchain")
FINGERPRINT_FIELDS = (
    "source_tree", "build_roots", "lakefile_sha256",
    "manifest_sha256", "toolchain",
)
REPOSITORY = "laurajoyhutchins/riemann-hypothesis-lean"
SHA40 = re.compile(r"[0-9a-f]{40}\Z")
MAX_INPUT_BYTES = 64 * 1024 * 1024


def git(root: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", "-C", str(root), *args],
        check=True, capture_output=True, text=True,
    )
    return result.stdout.strip()


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical(data: object) -> bytes:
    return json.dumps(
        data, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
    ).encode("utf-8")


def fingerprint(fields: dict) -> str:
    """Same canonical input fingerprint convention as community CI."""
    if set(fields) != set(FINGERPRINT_FIELDS):
        raise ValueError("cache fingerprint requires precisely five input fields")
    return digest(canonical(fields))


def regular_input(root: Path, name: str) -> bytes:
    path = root / name
    if path.is_symlink() or not path.is_file():
        raise ValueError(f"input must be a regular tracked file: {name}")
    size = path.stat().st_size
    if size > MAX_INPUT_BYTES:
        raise ValueError(f"oversized build input: {name}")
    return path.read_bytes()


def source_identity(root: Path, *, repository: str = REPOSITORY) -> dict:
    if repository != REPOSITORY:
        raise ValueError("identity is scoped to this fork, not an upstream cache receipt")
    root = root.resolve(strict=True)
    if (root / "src").is_symlink() or not (root / "src").is_dir():
        raise ValueError("missing regular RH source directory")
    # Strictly require all proof source and config bytes to match a Git commit.
    # Otherwise HEAD:src could describe *different* contents from the checkout.
    status = git(root, "status", "--porcelain", "--untracked-files=all",
                 "--", "src", *INPUTS)
    if status:
        raise ValueError("uncommitted or untracked proof/config inputs")
    ignored = git(root, "ls-files", "--others", "--ignored",
                  "--exclude-standard", "--", "src")
    if ignored:
        raise ValueError("ignored file under src may influence proof elaboration")
    for name in INPUTS:
        git(root, "ls-files", "--error-unmatch", "--", name)
    files = {name: regular_input(root, name) for name in INPUTS}
    head = git(root, "rev-parse", "--verify", "HEAD")
    tree = git(root, "rev-parse", "--verify", "HEAD^{tree}")
    src = git(root, "rev-parse", "--verify", "HEAD:src")
    if any(SHA40.fullmatch(x) is None for x in (head, tree, src)):
        raise ValueError("unexpected Git object format for community CI identity")
    if git(root, "cat-file", "-t", src) != "tree":
        raise ValueError("source identity must name a Git tree")
    toolchain = files["lean-toolchain"].decode("utf-8").strip()
    if not toolchain.startswith("leanprover/lean4:v"):
        raise ValueError("unexpected unpinned Lean toolchain")
    fields = {
        "source_tree": src,
        "build_roots": {},
        "lakefile_sha256": digest(files["lakefile.toml"]),
        "manifest_sha256": digest(files["lake-manifest.json"]),
        "toolchain": toolchain,
    }
    return {
        "schema": 1,
        "repository": repository,
        "candidate_head": head,
        "candidate_tree": tree,
        **fields,
        "input_fingerprint": fingerprint(fields),
        "proof_verified": False,
        "purpose": "cache candidate identity only; not a build, proof check or cache acceptance",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path("."))
    parser.add_argument("--output", type=Path, required=True)
    options = parser.parse_args()
    result = source_identity(options.root)
    options.output.parent.mkdir(parents=True, exist_ok=True)
    options.output.write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
