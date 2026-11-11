"""Checks relevant to errors that could invalidate the finite certificate."""
import unittest
from fractions import Fraction
from decimal import Decimal
try:
    from .screw_interval import I, Screw, prime_powers, gap_max
except ImportError:  # Direct execution and unittest discovery from research/.
    from screw_interval import I, Screw, prime_powers, gap_max


class Checks(unittest.TestCase):
    def test_rational_rounding_and_arithmetic(self):
        # Oracle is exact Fraction arithmetic, not another floating library.
        for a in (Fraction(-7, 13), Fraction(1, 3), Fraction(19, 11)):
            for b in (Fraction(-4, 7), Fraction(2, 5), Fraction(17, 23)):
                for interval, exact in ((I(a)+I(b), a+b),
                                        (I(a)-I(b), a-b),
                                        (I(a)*I(b), a*b),
                                        (I(a)/I(b), a/b)):
                    self.assertLessEqual(Fraction(interval.lo), exact)
                    self.assertGreaterEqual(Fraction(interval.hi), exact)

    def test_prime_powers_are_complete_unique(self):
        self.assertEqual(prime_powers(32),
                         [(2, 2), (3, 3), (4, 2), (5, 5), (7, 7),
                          (8, 2), (9, 3), (11, 11), (13, 13), (16, 2),
                          (17, 17), (19, 19), (23, 23), (25, 5),
                          (27, 3), (29, 29), (31, 31), (32, 2)])

    def test_startup_and_independent_derivative_expression(self):
        s = Screw()
        self.assertLess(s.smooth(I('0.5')).hi, Decimal('-0.025'))
        for t in ('0.5', '1', '2', '4'):
            x = (-I(t)/2).exp()
            # H'=-2(e^(t/2)-e^(-t/2))+C-atanh(x)-atan(x).
            # Compute the last two from their combined integral expansion.
            series, power, x4 = I(0), x, x.square().square()
            for k in range(300):
                series += 2*power/(4*k+1)
                power *= x4
            tail = 2*power/((4*300+1)*(1-x4))
            series += I(0, tail.hi)
            other = -2*((I(t)/2).exp()-x)+s.c-series
            direct = s.smooth(I(t), derivative=True)
            self.assertLessEqual(direct.lo, other.hi)
            self.assertLessEqual(other.lo, direct.hi)

    def test_gap_upper_bounds_cover_independent_samples(self):
        s, a, b = Screw(), I(0), I(0)
        left = I('0.5')
        for q, p in prime_powers(20):
            right = I(q).ln()
            result, _, _ = gap_max(s, left, right, a, b)
            for k in range(11):
                sample = left+(right-left)*I(Fraction(k, 10))
                # Sampling is only a regression check for the analytic bound.
                self.assertLessEqual(s.value(sample, a, b).lo, result.hi)
            w = I(p).ln()/I(q).sqrt()
            old_endpoint = s.value(right, a, b)
            a, b = a+w, b+w*right
            new_endpoint = s.value(right, a, b)
            self.assertLessEqual(old_endpoint.lo, new_endpoint.hi)
            self.assertLessEqual(new_endpoint.lo, old_endpoint.hi)
            left = right


if __name__ == '__main__':
    unittest.main()
