"""Regression checks for the exploratory toy model of post-widder-map.txt."""
from fractions import Fraction
import unittest

try:
    from .postwidder_toy import (ON_LINE, first_violation, limit_constant,
                                 normalised_derivative, threshold)
except ImportError:
    from postwidder_toy import (ON_LINE, first_violation, limit_constant,
                                normalised_derivative, threshold)


class ToyModel(unittest.TestCase):
    def test_threshold_is_the_circle_condition(self):
        # |w - (b + i a)| < w  <=>  w > (a^2+b^2)/(2b), exactly.
        for a, b in ((Fraction(40), Fraction(2, 5)), (Fraction(7), Fraction(1, 3))):
            w_star = (a*a+b*b)/(2*b)
            for w in (w_star*Fraction(9, 10), w_star*Fraction(11, 10)):
                inside = (w-b)**2+a*a < w*w
                self.assertEqual(inside, w > w_star)
            self.assertAlmostEqual(threshold(float(a), float(b)), float(w_star))

    def test_pole_modulus_identity(self):
        # |1 - p/w|^2 = 1 - 2b(w-w*)/w^2 for p = b + i a (note, (2.a)).
        for a, b, w in ((Fraction(40), Fraction(2, 5), Fraction(3000)),
                        (Fraction(9), Fraction(1, 4), Fraction(50)),
                        (Fraction(9), Fraction(1, 4), Fraction(500))):
            w_star = (a*a+b*b)/(2*b)
            modulus_squared = (1-b/w)**2+(a/w)**2
            self.assertEqual(modulus_squared, 1-2*b*(w-w_star)/(w*w))
            self.assertGreater((1+b/w)**2+(a/w)**2, 1)

    def test_low_orders_match_direct_formula(self):
        # c_0 = w L(w) and c_1 = -w^2 L'(w) for the toy sum, computed
        # directly from 2/(w(w^2+gamma^2)).
        a, b, w = 40.0, 0.4, 37.5
        gammas = [complex(t) for t in ON_LINE]+[complex(a, -b), complex(a, b)]
        value = sum(2/(w*(w*w+g*g)) for g in gammas).real
        slope = sum(-2*(1/(w*w*(w*w+g*g))+2/(w*w+g*g)**2) for g in gammas).real
        self.assertAlmostEqual(normalised_derivative(0, w, a, b), w*value, 12)
        self.assertAlmostEqual(normalised_derivative(1, w, a, b),
                               -w*w*slope, 12)

    def test_below_threshold_converges_to_residue(self):
        w = 0.5*threshold(40.0, 0.4)
        # Observation for this toy; Proposition E alone does not imply it.
        self.assertIsNone(first_violation(w, 3000))
        # Proposition E: convergence to the residue, far out.
        far = normalised_derivative(int(w*w), w)
        self.assertAlmostEqual(far, limit_constant(), 6)

    def test_above_threshold_is_violated_only_at_high_order(self):
        w = 2*threshold(40.0, 0.4)
        self.assertIsNone(first_violation(w, 2000))
        # A sign change exists further out; locate one by coarse sampling.
        negative = [n for n in range(40000, 80000, 7)
                    if normalised_derivative(n, w) < 0]
        self.assertTrue(negative)

    def test_no_off_line_zero_means_no_violation(self):
        # With the offset removed the same height is an on-line zero and
        # every term is nonnegative.
        for w in (10.0, 500.0, 8000.0):
            for order in (0, 1, 5, 50, 5000, 200000):
                self.assertGreaterEqual(
                    normalised_derivative(order, w, 40.0, 0.0), 0.0)


if __name__ == '__main__':
    unittest.main()
