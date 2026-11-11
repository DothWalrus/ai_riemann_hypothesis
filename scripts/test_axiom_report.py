import unittest
from check_axiom_report import check


class AxiomReportTests(unittest.TestCase):
    def test_standard_foundations(self):
        self.assertTrue(check("'RhCertificates.tangent_negative' depends on axioms: "
                              "[propext, Classical.choice, Quot.sound]"))

    def test_axiom_free(self):
        self.assertTrue(check("'RhCertificates.tangent_negative' does not depend on any axioms"))

    def test_rejects_holes_and_new_axioms(self):
        for name in ('sorryAx', 'RH_is_true', 'Lean.ofReduceBool'):
            with self.subTest(name=name), self.assertRaises(ValueError):
                check("'RhCertificates.tangent_negative' depends on axioms: [" + name + "]")

    def test_rejects_missing_or_wrong_theorem(self):
        for text in ('', 'Build completed successfully',
                     "'FakeRhCertificates.tangent_negative' depends on axioms: [propext]"):
            with self.subTest(text=text), self.assertRaises(ValueError):
                check(text)


if __name__ == '__main__':
    unittest.main()
