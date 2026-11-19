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

    def test_named_declaration(self):
        name = 'RhCertificates.startup_negative_of_second_derivative_signs'
        self.assertTrue(check(f"'{name}' depends on axioms: [propext, Quot.sound]", name))

    def test_named_declaration_cannot_match_a_different_name(self):
        text = "'Other.RhCertificates.curvature_cubic_exp_bracket' depends on axioms: [propext]"
        with self.assertRaises(ValueError):
            check(text, 'RhCertificates.curvature_cubic_exp_bracket')

    def test_duplicate_report_with_hidden_hole_is_rejected(self):
        name = 'RhCertificates.exists_exponential_curvature_transition'
        text = (f"'{name}' depends on axioms: [propext]\n"
                f"'{name}' depends on axioms: [sorryAx]")
        with self.assertRaises(ValueError):
            check(text, name)


if __name__ == '__main__':
    unittest.main()
