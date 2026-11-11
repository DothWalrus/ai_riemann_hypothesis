"""Regression tests for certificate failure modes and finite input bounds."""
from decimal import Decimal
from fractions import Fraction
from pathlib import Path
import subprocess
import sys
import unittest

try:
    from .screw_interval import I
    from .zero_tail_certificate import cosine
except ImportError:
    from screw_interval import I
    from zero_tail_certificate import cosine


ROOT = Path(__file__).resolve().parents[1]


class SafetyChecks(unittest.TestCase):
    def test_optimized_python_is_rejected(self):
        for filename in ('ns_startup_certificate.py',
                         'research/screw_interval.py',
                         'research/zero_tail_certificate.py',
                         'research/kernel_control.py'):
            result = subprocess.run([sys.executable, '-O', str(ROOT/filename)],
                                    cwd=ROOT, capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0, filename)
            self.assertIn('do not use python -O', result.stderr, filename)

    def test_invalid_interval_and_zero_divisor_are_rejected(self):
        with self.assertRaises(AssertionError):
            I(2, 1)
        with self.assertRaises(AssertionError):
            I(1)/I(-1, 1)
        from ns_startup_certificate import I as StartupI
        with self.assertRaises(AssertionError):
            StartupI(2, 1)

    def test_square_straddling_zero(self):
        square = I(-2, 3).square()
        self.assertEqual(square.lo, 0)
        self.assertGreaterEqual(square.hi, 9)

    def test_cosine_known_values_and_zero_truncation(self):
        # Independent exact values at zero and integer multiples of pi
        # catch sign, factor-two and argument-reduction regressions.
        from ns_startup_certificate import I as StartupI, atan
        pi = 16*atan(StartupI(1)/5)-4*atan(StartupI(1)/239)
        for k in (-5, -2, -1, 0, 1, 2, 5):
            value = cosine(k*pi, pi)
            expected = Decimal((-1)**k)
            self.assertLessEqual(value.lo, expected)
            self.assertGreaterEqual(value.hi, expected)
        printed = [
            '14.1347251417346937904572519835625',
            '21.0220396387715549926284795938969',
            '25.0108575801456887632137909925628',
            '30.4248761258595132103118975305840',
            '32.9350615877391896906623689640747',
        ]
        source_radius = Fraction(1, 2**102)
        code_radius = Fraction(1, 10**26)
        for text in printed:
            published = Fraction(Decimal(text))
            truncated = Fraction(Decimal(text[:29]))
            self.assertLess(abs(published-truncated)+source_radius, code_radius)


if __name__ == '__main__':
    unittest.main()
