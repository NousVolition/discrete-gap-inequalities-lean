"""Regression checks for the axiom audit's acceptance and rejection behavior."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

CHECKER = Path(__file__).with_name('check_axioms.py')

class AxiomAuditTests(unittest.TestCase):
    def audit(self, source, output):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'input.lean').write_text(source, encoding='utf-8')
            (root / 'output.txt').write_text(output, encoding='utf-8')
            return subprocess.run([sys.executable, '-X', 'utf8', str(CHECKER),
                str(root / 'input.lean'), str(root / 'output.txt')],
                capture_output=True, text=True, encoding='utf-8')

    def test_apostrophes_and_axiom_free_reports(self):
        result = self.audit("#print axioms Demo.sum'\n#print axioms Demo.zero'\n",
            "'Demo.sum'' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
            "'Demo.zero'' does not depend on any axioms\n")
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn('2 declarations checked, 0 nonstandard, 0 missing', result.stdout)

    def test_nonstandard_axiom_in_apostrophe_name_is_rejected(self):
        result = self.audit("#print axioms Demo.bad'\n",
            "'Demo.bad'' depends on axioms: [sorryAx]\n")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("NONSTANDARD AXIOM Demo.bad'", result.stdout)

    def test_missing_report_is_rejected(self):
        result = self.audit("#print axioms Demo.missing'\n", '')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("NO AXIOM REPORT Demo.missing'", result.stdout)

    def test_unrelated_report_does_not_cover_wanted_name(self):
        result = self.audit('#print axioms Demo.wanted\n',
            "'Demo.other' depends on axioms: []\n")
        self.assertNotEqual(result.returncode, 0)

    def test_empty_inventory_is_rejected(self):
        self.assertNotEqual(self.audit('', '').returncode, 0)

if __name__ == '__main__':
    unittest.main()
