"""Regressions for standalone module boundaries and safe source formatting."""

import contextlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import fmt
import lint


class ModuleBoundaryTests(unittest.TestCase):
    def graph(self):
        graph = {name: set() for name in lint.ENTRY_POINTS}
        graph.update({
            "Kalman/Definitions/Input.lean": set(),
            "Kalman/Implementation/Filter.lean": {"Kalman/Definitions/Input.lean"},
            "Kalman/Implementation/Correctness/Accuracy.lean": {
                "Kalman/Implementation/Filter.lean",
            },
            "Kalman/Proofs/Accuracy.lean": {
                "Kalman/Implementation/Correctness/Accuracy.lean",
            },
        })
        graph["Kalman.lean"] = {name for name in graph if name.startswith("Kalman/")
                                and not name.startswith("Kalman/Tests/")}
        for name in lint.ENTRY_POINTS:
            if name.startswith("Kalman/Tests/"):
                graph[name] = {"Kalman.lean"}
        return graph

    def test_valid_layers_and_test_entry_points(self):
        self.assertEqual(lint.layout_issues(self.graph()), [])

    def test_definition_cannot_reach_runtime_through_helper(self):
        graph = self.graph()
        graph["Kalman/Definitions/Input.lean"] = {"Kalman/Definitions/Helper.lean"}
        graph["Kalman/Definitions/Helper.lean"] = {"Kalman/Implementation/Filter.lean"}
        graph["Kalman/Implementation/Filter.lean"] = set()
        self.assertTrue(any("Kalman/Definitions/Input.lean: forbidden transitive"
                            in issue for issue in lint.layout_issues(graph)))

    def test_runtime_cannot_reach_correctness_through_helper(self):
        graph = self.graph()
        graph["Kalman/Implementation/Filter.lean"] = {"Kalman/Implementation/Helper.lean"}
        graph["Kalman/Implementation/Helper.lean"] = {
            "Kalman/Implementation/Correctness/Accuracy.lean",
        }
        graph["Kalman/Implementation/Correctness/Accuracy.lean"] = {
            "Kalman/Definitions/Input.lean",
        }
        self.assertTrue(any("Kalman/Implementation/Filter.lean: forbidden transitive"
                            in issue for issue in lint.layout_issues(graph)))

    def test_correctness_cannot_reach_proof(self):
        graph = self.graph()
        graph["Kalman/Implementation/Correctness/Accuracy.lean"] = {
            "Kalman/Proofs/Accuracy.lean",
        }
        graph["Kalman/Proofs/Accuracy.lean"] = {"Kalman/Definitions/Input.lean"}
        self.assertTrue(any("Correctness/Accuracy.lean: forbidden transitive"
                            in issue for issue in lint.layout_issues(graph)))

    def test_orphan_module_is_rejected(self):
        graph = self.graph()
        graph["Kalman/Proofs/Orphan.lean"] = set()
        self.assertTrue(any("outside the import closure" in issue
                            for issue in lint.layout_issues(graph)))

    def test_import_cycle_is_rejected(self):
        graph = self.graph()
        graph["Kalman/Proofs/Accuracy.lean"] = {"Kalman/Proofs/Accuracy.lean"}
        self.assertTrue(any("Import cycle" in issue for issue in lint.layout_issues(graph)))

    def test_result_imported_only_by_tests_is_not_public(self):
        graph = self.graph()
        graph["Kalman/Proofs/Hidden.lean"] = set()
        graph["Kalman/Tests/Specification.lean"].add("Kalman/Proofs/Hidden.lean")
        issues = lint.layout_issues(graph)
        self.assertTrue(any("does not expose Kalman/Proofs/Hidden.lean" in issue
                            for issue in issues))
        self.assertFalse(any("outside the import closure" in issue for issue in issues))


class FormatterSafetyTests(unittest.TestCase):
    def exercise(self, replacement, returncode=0):
        original = b"theorem sound : True := by\n  trivial\n"
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "Example.lean"
            source.write_bytes(original)

            def formatter(*args, **kwargs):
                source.write_bytes(replacement)
                return returncode

            with patch.object(fmt, "ROOT", root), patch.object(
                fmt.subprocess, "call", side_effect=formatter
            ), contextlib.redirect_stderr(io.StringIO()):
                result = fmt.format_files(["Example.lean"])
            return result, source.read_bytes(), original

    def test_changed_proof_is_restored_even_after_formatter_success(self):
        result, actual, original = self.exercise(b"theorem sound : False := by\n  sorry\n")
        self.assertEqual(result, 1)
        self.assertEqual(actual, original)

    def test_whitespace_formatting_is_kept(self):
        replacement = b"theorem sound : True :=\n    by trivial\n"
        result, actual, _ = self.exercise(replacement)
        self.assertEqual(result, 0)
        self.assertEqual(actual, replacement)

    def test_formatter_failure_is_not_hidden(self):
        result, _, _ = self.exercise(b"theorem sound : True := by\n  trivial\n", returncode=7)
        self.assertEqual(result, 7)


if __name__ == "__main__":
    unittest.main()
