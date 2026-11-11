"""Checks for the conditional 7/8 certificate and the reductions it uses."""
from decimal import Decimal
from fractions import Fraction
from pathlib import Path
import math
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT/'research'))
from ns_startup_certificate import I as StartupI, atan
import screw_interval
import zero_tail_seven_eighths as cert

ZEROS = [float(z) for z in cert.RAW_ZEROS]
TAIL = float(cert.TAIL_CONSTANT)


def deficit(t):
    return sum(2*(1-math.cos(z*t))/z**2 for z in ZEROS)


def intervals():
    pi = 16*atan(StartupI(1)/5)-4*atan(StartupI(1)/239)
    zeros = [StartupI(z)+StartupI('-1e-26', '1e-26') for z in cert.RAW_ZEROS]
    return pi, zeros


class ConditionalCertificate(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.pi, cls.zeros = intervals()
        cls.accepted, cls.attempts = cert.certify_range(
            cls.pi, cls.zeros, cert.OFFSET, cert.RANGE[0], cert.RANGE[1],
            cert.TAIL_CONSTANT)

    def test_optimized_python_is_rejected(self):
        result = subprocess.run(
            [sys.executable, '-O', str(ROOT/'research/zero_tail_seven_eighths.py')],
            cwd=ROOT, capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('do not use python -O', result.stderr)

    def test_script_passes(self):
        result = subprocess.run(
            [sys.executable, str(ROOT/'research/zero_tail_seven_eighths.py')],
            cwd=ROOT, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('(a) accepted cells: 388 attempts: 775', result.stdout)
        self.assertEqual(result.stdout.count('PASS'), 2)

    def test_cell_margin_matches_independent_formula(self):
        # Float oracle for D_5(c) - L r - (exp(offset*b)+1) A, with the
        # envelope at the RIGHT end and the Lipschitz term present. A
        # left-end envelope or a missing Lipschitz term changes the value
        # by far more than the tolerance.
        lipschitz = sum(2/z for z in ZEROS)
        for a, b, offset in ((40.0, 40.5, Fraction(3, 8)),
                             (51.25, 51.5, Fraction(3, 8)),
                             (57.5, 58.0, Fraction(3, 8)),
                             (41.0, 41.25, Fraction(1, 2))):
            value = cert.cell_margin(self.pi, self.zeros, offset,
                                     Decimal(repr(a)), Decimal(repr(b)),
                                     cert.TAIL_CONSTANT)
            expected = (deficit((a+b)/2)-lipschitz*(b-a)/2
                        - (math.exp(float(offset)*b)+1)*TAIL)
            self.assertLess(float(value.hi)-float(value.lo), 1e-30)
            self.assertAlmostEqual(float(value.lo), expected, 12)
            left_end = (deficit((a+b)/2)-lipschitz*(b-a)/2
                        - (math.exp(float(offset)*a)+1)*TAIL)
            self.assertGreater(abs(left_end-expected), 1e-6)

    def test_accepted_cells_tile_the_range(self):
        ordered = sorted(self.accepted)
        self.assertEqual(len(ordered), 388)
        self.assertEqual(self.attempts, 775)
        self.assertEqual(ordered[0][0], Decimal(40))
        self.assertEqual(ordered[-1][1], Decimal(58))
        for left, right in zip(ordered, ordered[1:]):
            self.assertEqual(left[1], right[0])

    def test_certified_margin_is_below_sampled_truth(self):
        # In every accepted cell the true D_5(t) - envelope(t), sampled in
        # floats, must be at least the certified margin.
        for a, b, margin in self.accepted:
            left, right = float(a), float(b)
            for k in range(9):
                t = left+(right-left)*k/8
                truth = deficit(t)-(math.exp(0.375*t)+1)*TAIL
                self.assertGreaterEqual(truth, float(margin)-1e-12)
            self.assertGreater(margin, 0)

    def test_exponent_is_outward_and_exact_when_possible(self):
        exact = cert.exponent_times(Fraction(3, 8), StartupI(58))
        self.assertEqual((exact.lo, exact.hi),
                         (Decimal('21.75'), Decimal('21.75')))
        third = cert.exponent_times(Fraction(1, 3), StartupI(1))
        self.assertLessEqual(Fraction(third.lo), Fraction(1, 3))
        self.assertGreaterEqual(Fraction(third.hi), Fraction(1, 3))

    def test_constant_k_bound(self):
        # K = sum_{k>=1} 1/(4(k+1/4)^2) <= 9/25, by partial sum plus the
        # integral bound 1/(4(N+1/4)) for the remainder.
        terms = 2000
        partial = sum(Fraction(1, 4)/(Fraction(4*k+1, 4))**2
                      for k in range(1, terms+1))
        remainder = Fraction(1, 4)/Fraction(4*terms+1, 4)
        self.assertLess(partial+remainder, Fraction(9, 25))
        self.assertGreater(partial, Fraction(29, 100))

    def test_method_fails_without_the_seven_eighths_input(self):
        # With the unconditional exponent 1/2 the five-zero certificate must
        # refuse near t = 58, through its minimum-width guard.
        with self.assertRaises(AssertionError) as caught:
            cert.certify_range(self.pi, self.zeros, Fraction(1, 2),
                               Decimal(57), Decimal(58), cert.TAIL_CONSTANT)
        a, b, margin = caught.exception.args[0]
        self.assertLessEqual(b-a, Decimal('1e-8'))
        self.assertLess(margin.hi, 0)

    def test_j_minorant_changes_sign_just_beyond_the_limits(self):
        # j_margin is the script's LOWER bound for h (C low, K high, A
        # high). It is positive at the stated limits and negative one unit
        # later, so 62 and 83 are the largest integers this minorant gives.
        # This says nothing about the sign of h itself beyond the limits.
        c_low = screw_interval.constants()[3].lo
        for offset, limit in ((Fraction(1, 2), cert.J_LIMIT_UNCONDITIONAL),
                              (Fraction(3, 8), cert.J_LIMIT_SEVEN_EIGHTHS)):
            inside = cert.j_margin(c_low, offset, StartupI(limit),
                                   cert.TAIL_CONSTANT)
            beyond = cert.j_margin(c_low, offset, StartupI(limit+1),
                                   cert.TAIL_CONSTANT)
            self.assertGreater(inside.lo, 0)
            self.assertLess(beyond.hi, 0)

    def test_chebyshev_identity_from_the_definition_of_j(self):
        # chebyshev-error.txt, formula (B):
        #   g(log x) = J(x) + (C-1) log x - K + R(x),
        # with J computed FROM ITS DEFINITION
        #   J(x) = int_1^x (psi(u) - u) u^(-3/2) [1 + log(x/u)/2] du
        # by Simpson quadrature between prime powers, and g from the
        # prime-side interval code. No zero data. This exercises the
        # Stieltjes step as well as the constants.
        screw = screw_interval.Screw()
        c = float(screw.c.lo)
        k_const = sum(1/(4*(k+0.25)**2) for k in range(1, 200000))+1/800000
        events = screw_interval.prime_powers(400)

        def integrand(u, psi, x):
            return (psi-u)*u**-1.5*(1+math.log(x/u)/2)

        def simpson(lo, hi, psi, x, steps=400):
            h = (hi-lo)/steps
            total = integrand(lo, psi, x)+integrand(hi, psi, x)
            total += 4*sum(integrand(lo+(2*i+1)*h, psi, x)
                           for i in range(steps//2))
            total += 2*sum(integrand(lo+2*i*h, psi, x)
                           for i in range(1, steps//2))
            return total*h/3

        for x in (1.5, 2.0, 3.5, 10.5, 50.5, 300.5):
            t = math.log(x)
            breaks = [1.0]+[float(q) for q, _ in events if q < x]+[x]
            psi, j, a, b = 0.0, 0.0, 0.0, 0.0
            for lo, hi in zip(breaks, breaks[1:]):
                for q, p in events:
                    if q == lo:
                        psi += math.log(p)
                        w = math.log(p)/math.sqrt(q)
                        a += w
                        b += w*math.log(q)
                j += simpson(lo, hi, psi, x)
            if x <= 2:
                # Elementary case quoted in the note.
                self.assertAlmostEqual(j, -4*math.sqrt(x)+t+4, 9)
            if x >= 2:
                g = float(screw.value(screw_interval.I(repr(t)),
                                      screw_interval.I(repr(a)),
                                      screw_interval.I(repr(b))).lo)
                r = sum(x**(-2*k-0.5)/(4*(k+0.25)**2) for k in range(1, 60))
                self.assertAlmostEqual(g, j+(c-1)*t-k_const+r, 8)
            self.assertLess(j, 0)


if __name__ == '__main__':
    unittest.main()
