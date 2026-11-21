#!/usr/bin/env python3
"""Inspect an explicit pair of Lean theorem bodies and module import direction.

This is a source evidence tool. It neither elaborates Lean nor proves
theorems equivalent. It fails closed on ambiguous/missing declarations.
"""
import argparse
import difflib
import json
from pathlib import Path
import re

DECL = re.compile(r"^(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s+([^\s(:{]+)")
TOP = re.compile(r"^(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom|example|namespace|section|end|variable|open|attribute|set_option)\b")
IMPORT = re.compile(r"^import\s+(.+)$")


def read_decl(file: Path, name: str):
    lines = file.read_text(encoding="utf-8").splitlines()
    matches = [i for i, line in enumerate(lines) if
               (m := DECL.match(line)) and m.group(1) == name]
    if len(matches) != 1:
        raise ValueError(f"{file}: expected exactly one {name}, found {len(matches)}")
    start = matches[0]
    end = next((i for i in range(start + 1, len(lines)) if TOP.match(lines[i])), len(lines))
    body = "\n".join(lines[start:end])
    marker = body.find(":= by")
    if marker < 0:
        raise ValueError(f"{file}: {name} has no explicit ':= by'")
    return {"path": file.as_posix(), "start": start + 1, "end": end,
            "statement": body[:marker].strip(),
            "proof": body[marker + len(":= by"):].strip(),
            "imports": [m.group(1).split() for line in lines if (m := IMPORT.match(line))]}


def compare(a, b):
    proof_a = a["proof"].splitlines()
    proof_b = b["proof"].splitlines()
    matcher = difflib.SequenceMatcher(a=proof_a, b=proof_b, autojunk=False)
    matching = sum(block.size for block in matcher.get_matching_blocks())
    a_imports = set(sum(a["imports"], []))
    b_imports = set(sum(b["imports"], []))
    return {
        "left": {k: a[k] for k in ("path", "start", "end")},
        "right": {k: b[k] for k in ("path", "start", "end")},
        "proof_lines_left": len(proof_a),
        "proof_lines_right": len(proof_b),
        "matching_proof_lines_in_order": matching,
        "proof_text_identical": a["proof"] == b["proof"],
        "statements_text_identical": a["statement"] == b["statement"],
        "left_direct_imports": sorted(a_imports),
        "right_direct_imports": sorted(b_imports),
        "classification": "source evidence only; no theorem equivalence or kernel check",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--src", type=Path, default=Path("src"))
    parser.add_argument("--left", required=True, help="path relative to src, without .lean")
    parser.add_argument("--right", required=True, help="path relative to src, without .lean")
    parser.add_argument("--left-theorem", required=True)
    parser.add_argument("--right-theorem", required=True)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    for mod in (args.left, args.right):
        if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(?:[./][A-Za-z_][A-Za-z_0-9]*)*", mod):
            parser.error(f"invalid module path: {mod}")
    def read(mod, theorem):
        file = args.src / (mod.replace(".", "/") + ".lean")
        if not file.is_file():
            parser.error(f"missing source file: {file}")
        return read_decl(file, theorem)
    a = read(args.left, args.left_theorem)
    b = read(args.right, args.right_theorem)
    result = compare(a, b)
    result["left_module"] = args.left.replace("/", ".")
    result["right_module"] = args.right.replace("/", ".")
    result["left_imports_right"] = result["right_module"] in result["left_direct_imports"]
    result["right_imports_left"] = result["left_module"] in result["right_direct_imports"]
    print(json.dumps(result, indent=2))
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
