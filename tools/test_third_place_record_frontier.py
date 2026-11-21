"""Hermetic tests for field-frontier source evidence, not Lean proof checks."""
import unittest

from third_place_record_frontier import (
    SITES,
    RECORD_FILE,
    RECORD_CONSTRUCTOR,
    analyze_sources,
    direct_field_projection,
    read_constructor_fields,
    theorem_slice,
    whole_record_contexts,
)


class FieldFrontierTests(unittest.TestCase):
    def sample(self):
        record = (
            "theorem " + RECORD_CONSTRUCTOR + " (O : Unit) : Bundle where\n"
            "  green := trivial\n"
            "  depthZeroSupport' := trivial\n"
            "  other := trivial\n"
            "end\n"
        )
        sample = {
            RECORD_FILE: record
        }
        for file, theorem in SITES:
            sample.setdefault(file, "")
            if theorem == "hypotheses_nonempty_of_unramified_exponents_alt":
                body = (
                    "theorem " + theorem + " : True := by\n"
                    "  intro P\n"
                    "  have a := P.depthZeroSupport'\n"
                    "  exact anyFunction P\n"
                )
            elif theorem == "open_orbit_of_unramified_exponents_alt":
                body = (
                    "theorem " + theorem + " : True := by\n"
                    "  intro P\n"
                    "  have a := P.other\n"
                    "  trivial\n"
                )
            else:
                body = (
                    "theorem " + theorem + " : True := by\n"
                    "  intro P\n"
                    "  have a := P.green\n"
                    "  trivial\n"
                )
            sample[file] += body + "\n"
        return sample

    def test_source_constructor_and_field_frontier(self):
        report = analyze_sources(self.sample(), expect_fields=3)
        self.assertEqual(report["record_field_count"], 3)
        self.assertEqual(report["direct_field_union_count"], 3)
        self.assertEqual(report["whole_record_occurrences_across_slices"], 1)
        by = {r["theorem"]: r for r in report["proof_sites"]}
        sub = by["hypotheses_nonempty_of_unramified_exponents_alt"]
        self.assertIn("depthZeroSupport'", sub["directly_referenced_fields"])
        self.assertEqual(sub["whole_record_occurrence_count"], 1)

    def test_type_level_record_not_source_of_truth(self):
        src = self.sample()
        src[RECORD_FILE] = src[RECORD_FILE].replace(
            "  other := trivial\n", ""
        )
        with self.assertRaisesRegex(ValueError, "field-count drift"):
            analyze_sources(src, expect_fields=3)

    def test_missing_theorem_rejected(self):
        with self.assertRaisesRegex(ValueError, "exactly one"):
            theorem_slice("theorem unrelated : True := by trivial", "missing")

    def test_derived_accessor_not_mistaken_for_record_field(self):
        src = self.sample()
        key = "SiegelEisensteinSecondTermHypotheses.lean"
        src[key] = src[key].replace("P.green", "P.ghost")
        report = analyze_sources(src, expect_fields=3)
        self.assertIn("ghost", report["nonconstructor_dot_accessors_across_slices"])
        self.assertNotIn("ghost", report["direct_fields_seen_across_slices"])
        self.assertEqual(report["record_field_count"], 3)

    def test_comments_not_conflated_with_proof_calls(self):
        proof = "theorem q : True := by\n  intro P\n  have a := P.green -- P.other\n  exact use P"
        self.assertEqual(direct_field_projection(proof), {"green": 1})
        self.assertEqual(len(whole_record_contexts(proof)), 1)

    def test_rejects_duplicate_constructor_fields(self):
        s = self.sample()[RECORD_FILE].replace(
            "  other := trivial\n", "  green := trivial\n"
        )
        with self.assertRaisesRegex(ValueError, "duplicate field"):
            read_constructor_fields(s)


if __name__ == "__main__":
    unittest.main()
