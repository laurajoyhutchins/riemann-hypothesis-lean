#!/usr/bin/env python3
"""Audit the complete RH Lean source and unchanged five-theorem source boundary.

Counts physical source lines without treating formatting as a minimization.
This deliberately does not claim kernel proof verification.
"""
import argparse
import json
from pathlib import Path

NAMES = (
    "riemannHypothesis",
    "riemannZeta_eq_zero_re",
    "LFunction_ne_zero_of_half_lt_re",
    "LFunction_eq_zero_re",
    "LFunction_eq_zero_re_of_isPrimitive",
)
EXPECTED = (
    "theorem riemannHypothesis : RiemannHypothesis := rhOfAll",
    "theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := rhOfAll",
    "theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := allChi",
    "theorem LFunction_eq_zero_re : DirichletLZerosOnLine := claimAll.2.1",
    "theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine := critAll",
)


def count(src: Path) -> dict:
    if not src.is_dir():
        raise ValueError(f"missing Lean source root: {src}")
    files = lines = nonblank = bytes_total = 0
    for path in src.rglob("*.lean"):
        if not path.is_file():
            continue
        raw = path.read_bytes()
        files += 1
        bytes_total += len(raw)
        lines += raw.count(b"\n") + int(bool(raw) and not raw.endswith(b"\n"))
        nonblank += sum(bool(line.strip()) for line in raw.splitlines())
    if files == 0:
        raise ValueError("no Lean files found")
    return {
        "files": files,
        "physical_lines": lines,
        "nonblank_lines": nonblank,
        "source_bytes": bytes_total,
    }


def verify_surface(main: Path) -> None:
    lines = main.read_text(encoding="utf-8").splitlines()
    actual = [x.strip() for x in lines if x.lstrip().startswith("theorem ")]
    if actual != list(EXPECTED):
        raise ValueError(
            f"five Main theorem source lines changed: expected {EXPECTED}, got {actual}"
        )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--src", type=Path, default=Path("src"))
    parser.add_argument("--out", type=Path, default=Path("analysis/rh-source-inventory.json"))
    args = parser.parse_args()
    verify_surface(args.src / "Main.lean")
    result = count(args.src)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
