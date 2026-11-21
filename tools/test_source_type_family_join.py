"""Synthetic tests for conservative original-export type/source attribution."""
import gzip
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from source_type_family_join import (
    EXPECTED_EXPORT_SHA, find_source_declarations, load_export_types, rank
)


def fixture(root: Path):
    counts = root / "counts.json"
    counts.write_text(json.dumps({"compressed_input_sha256": EXPECTED_EXPORT_SHA}))
    types = root / "families.tsv.gz"
    with gzip.open(types, "wt") as f:
        f.write("type_expr\tlevel_params\tfamily_size\tname\n")
        f.write("100\tu_1\t3\tN.first\n")
        f.write("100\tu_1\t3\tN.second\n")
        f.write("100\tu_1\t3\tN.third._simp_1\n")
        f.write("101\tu_1\t2\tN.unrelated\n")
    return types, counts


class SourceTypeFamilyJoinTests(unittest.TestCase):
    def test_join_preserves_distinct_exported_type_signature(self):
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            types, counts = fixture(root)
            index, stats = load_export_types(types, counts)
            self.assertEqual(stats["excluded_generated_or_private"], 1)
            src = root / "src"
            subtree = src / "Development/AbelianVarietyTheory/Proofs"
            subtree.mkdir(parents=True)
            (subtree / "A.lean").write_text(
                "namespace N\n"
                "theorem first : True := by\n  trivial\n"
                "end N\n", encoding="utf-8"
            )
            (subtree / "B.lean").write_text(
                "section\n"
                "namespace N\n"
                "theorem second : True := by\n  trivial\n"
                "end N\n"
                "end\n"
                "theorem unrelated : True := by\n  trivial\n",
                encoding="utf-8"
            )
            mapped, obs = find_source_declarations(
                src, "Development/AbelianVarietyTheory/Proofs", index
            )
            self.assertEqual(set(mapped), {"N.first", "N.second"})
            self.assertEqual(obs["matched_export_names_to_unique_source_proofs"], 2)
            ranked = rank(mapped, index, min_lines=2, limit=10)
            self.assertEqual(ranked["qualified_families_before_limit"], 1)
            self.assertEqual(ranked["families"][0]["members_mapped_to_source"], 2)

    def test_invalid_pinned_export_fails_closed(self):
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            types, counts = fixture(root)
            counts.write_text(json.dumps({"compressed_input_sha256": "wrong"}))
            with self.assertRaises(ValueError):
                load_export_types(types, counts)

    def test_duplicate_source_name_fails_attribution(self):
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            types, counts = fixture(root)
            index, _ = load_export_types(types, counts)
            src = root / "src"
            subtree = src / "Development/AbelianVarietyTheory/Proofs"
            subtree.mkdir(parents=True)
            for filename in ("A.lean", "B.lean"):
                (subtree / filename).write_text(
                    "namespace N\n"
                    "theorem first : True := by\n  trivial\n"
                    "end N\n", encoding="utf-8"
                )
            mapped, stats = find_source_declarations(
                src, "Development/AbelianVarietyTheory/Proofs", index
            )
            self.assertNotIn("N.first", mapped)
            self.assertEqual(stats["ambiguous_duplicate_source_declarations"], 1)


if __name__ == "__main__":
    unittest.main()
