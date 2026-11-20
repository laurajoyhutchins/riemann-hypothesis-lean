#!/usr/bin/env python3
"""Measure actual RH Lean source structure before choosing a large refactor.

Run on the full original source tree, not a synthetic sample.
This is *not* a theorem proof or permission to remove a declaration.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import re

DECL = re.compile(r"^\s*(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|example|noncomputable\s+def)\b", re.M)
THM = re.compile(r"^\s*(?:theorem|lemma)\b", re.M)
FORWARD = re.compile(r"\bfirst\s*\|\s*exact\s+@?_root_\.")
IMPORT = re.compile(r"^\s*(?:public\s+|private\s+)?import\b")
BOILERPLATE = re.compile(r"^\s*(?:set_option|open|section\b|end\b|namespace\b|variable\b|attribute\b|noncomputable section)")
DECL_HEADER = re.compile(r"^\s*(?:theorem|lemma|def|instance|abbrev|class|structure|inductive)\b")
LINES = ("physical", "nonblank", "import", "boilerplate", "theorem_headers", "forwarder_lines")


def audit(src: Path) -> dict:
    names = {str(p.relative_to(src)) for p in src.rglob("*.lean")}
    dimensions = defaultdict(Counter)
    kinds = Counter()
    sizes = Counter()
    family = Counter()
    pairs = Counter()
    examples: dict[str, list[str]] = defaultdict(list)
    big = []
    import_fanout = Counter()
    exact_files = Counter()
    single_forward = []
    repeated_declaration_headers = Counter()
    forbidden = []
    for n in sorted(names):
        raw = (src / n).read_bytes()
        text = raw.decode("utf-8")
        rows = text.splitlines()
        physical = len(rows)
        nonblank = sum(bool(row.strip()) for row in rows)
        imports = sum(bool(IMPORT.match(row)) for row in rows)
        boilerplate = sum(bool(BOILERPLATE.match(row)) for row in rows)
        theorems = len(THM.findall(text))
        decls = len(DECL.findall(text))
        forward = bool(FORWARD.search(text))
        forward_lines = len(rows) if forward and theorems == 1 else 0
        category = (
            "statement_paired" if n.endswith("Statement.lean") and n[:-len("Statement.lean")] + ".lean" in names
            else "statement_unpaired" if n.endswith("Statement.lean")
            else "statement_other" if "Statement" in Path(n).name
            else "other"
        )
        if forward and theorems == 1:
            category2 = "single_theorem_forward"
        else:
            category2 = "ordinary"
        root = Path(n).parts[0]
        prefix = "/".join(Path(n).parts[:3])
        stat = Counter(files=1, physical=physical, nonblank=nonblank, imports=imports,
                       boilerplate=boilerplate, theorems=theorems, declarations=decls,
                       forwarder_lines=forward_lines)
        for k in ["all", "root:"+root, "prefix:"+prefix, category, category2]:
            dimensions[k].update(stat)
        if category == "statement_paired":
            pairs["all"] += 1
            pairs["forward"] += int(forward)
            pairs["single_theorem"] += int(theorems == 1)
            pairs["single_theorem_forward"] += int(forward and theorems == 1)
            if forward and theorems == 1 and len(examples["paired_forward"]) < 15:
                examples["paired_forward"].append(n)
            elif not forward and len(examples["paired_nonforward"]) < 15:
                examples["paired_nonforward"].append(n)
        kinds["theorems"] += theorems
        kinds["declarations_textual"] += decls
        kinds["single_theorem_files"] += int(theorems == 1)
        kinds["single_forward_files"] += int(forward and theorems == 1)
        if forward and theorems == 1:
            single_forward.append((n, physical))
        if len(rows) > 200:
            big.append((physical, n))
        if decls == 0 and physical > 0:
            exact_files["no_declaration_file_lines"] += physical
            exact_files["no_declaration_files"] += 1
        if text.count("sorry") or text.count("admit"):
            if len(forbidden) < 10:
                forbidden.append(n)
        for line in rows:
            if DECL_HEADER.match(line) and len(line) > 40:
                # A bounded structural sketch. Do not infer mathematical
                # equality from matching syntax.
                skeleton = re.sub(r"\b[a-zA-Z_][a-zA-Z0-9_']*\b", "N", line.strip())
                repeated_declaration_headers[skeleton] += 1
    big.sort(reverse=True)
    single_forward.sort(key=lambda x: x[1], reverse=True)
    byroot = {key: dict(value) for key, value in sorted(dimensions.items()) if key.startswith("root:")}
    byprefix = sorted(((key, dict(value)) for key, value in dimensions.items() if key.startswith("prefix:")),
                      key=lambda item: item[1]["physical"], reverse=True)
    return {
        "files": len(names),
        "overall": dict(dimensions["all"]),
        "categories": {key: dict(dimensions[key]) for key in
                       ["statement_paired", "statement_unpaired", "statement_other",
                        "single_theorem_forward", "ordinary", "other"]},
        "paired_statement_counts": dict(pairs),
        "declaration_counts": dict(kinds),
        "no_decl": dict(exact_files),
        "by_root": byroot,
        "top_prefixes": byprefix[:40],
        "big_files": big[:30],
        "big_forward_files": single_forward[:30],
        "example_paths": dict(examples),
        "common_header_shapes": repeated_declaration_headers.most_common(30),
        "negative_scan_samples": forbidden,
        "important_limit": "Regex-based source archetypes, not verified semantics. Repetition and file shape alone do not warrant deletion."
    }


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--src", type=Path, default=Path("src"))
    p.add_argument("--out", type=Path, default=Path("analysis/rh-structural-profile.json"))
    args = p.parse_args()
    report = audit(args.src)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print("Overall", json.dumps(report["overall"], sort_keys=True))
    print("Categories", json.dumps(report["categories"], sort_keys=True))
    print("Paired statements", json.dumps(report["paired_statement_counts"], sort_keys=True))
    print("Top prefixes", json.dumps(report["top_prefixes"][:12], sort_keys=True))
    print("Representative paths", json.dumps(report["example_paths"], sort_keys=True))
    print("Largest files", json.dumps(report["big_files"][:15]))


if __name__ == "__main__":
    main()
