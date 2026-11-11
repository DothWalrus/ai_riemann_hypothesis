"""Exact-arithmetic checks of the identities in notes/laplace-second-order.txt.

Oracles are exact Fractions or Gaussian rationals, independent of the
Decimal interval code. They test the algebra the note relies on, not the
external zero inputs.
"""
from fractions import Fraction
from math import factorial
from pathlib import Path
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]


def phi(w, tau2):
    """One zero pair's term 2/(w(w^2+tau^2)) and its first two derivatives."""
    a = w*w+tau2
    return (2/(w*a),
            -2*(1/(w*w*a)+2/(a*a)),
            4/(w**3*a)+4/(w*a*a)+16*w/a**3)


def complex_power_inverse(re, im, n):
    """Real and imaginary parts of (re+i*im)^(-n), exactly."""
    x, y = Fraction(1), Fraction(0)
    for _ in range(n):
        x, y = x*re-y*im, x*im+y*re
    norm = x*x+y*y
    return x/norm, -y/norm


class Identities(unittest.TestCase):
    points = [(Fraction(1, 7), Fraction(3)), (Fraction(5, 2), Fraction(14)),
              (Fraction(20), Fraction(1413, 100)), (Fraction(9), Fraction(1, 3))]

    def test_derivative_formulas_by_exact_difference_quotients(self):
        # Symmetric difference quotients of a rational function, compared
        # with the closed forms to relative accuracy h^2.
        h = Fraction(1, 10**6)
        for w, tau in self.points:
            t2 = tau*tau
            value, first, second = phi(w, t2)
            up, down = phi(w+h, t2)[0], phi(w-h, t2)[0]
            self.assertLess(abs((up-down)/(2*h)-first), abs(first)/10**8)
            self.assertLess(abs((up-2*value+down)/(h*h)-second),
                            abs(second)/10**8)

    def test_single_zero_hankel_determinant(self):
        for w, tau in self.points:
            t2 = tau*tau
            value, first, second = phi(w, t2)
            a = w*w+t2
            exact = 4*(t2*t2+3*w**4)/(w**4*a**4)
            self.assertEqual(value*second-first*first, exact)
            # Lower bound used in Lemma C.
            self.assertGreaterEqual(exact, 3/(w**4*a*a))

    def test_partial_fraction_derivatives(self):
        # (-1)^n phi^(n)(w) = (2 n!/tau^2) [w^-(n+1) - Re (w-i tau)^-(n+1)].
        for w, tau in self.points:
            t2 = tau*tau
            for order, direct in enumerate(phi(w, t2)):
                real, _ = complex_power_inverse(w, -tau, order+1)
                formula = 2*factorial(order)/t2*(1/w**(order+1)-real)
                self.assertEqual((-1)**order*direct, formula)
                # Lemma A lower bound, squared to avoid a square root:
                # Re (w-i tau)^-(n+1) <= (w^2+tau^2)^(-(n+1)/2).
                self.assertLessEqual(real*real, 1/(w*w+t2)**(order+1))

    def test_l_derivative_algebra(self):
        # L = mu/w^2 with mu' = v, mu'' = c3, checked on a polynomial mu.
        w = Fraction(7, 3)
        coefficients = [Fraction(2), Fraction(-1, 5), Fraction(3, 7), Fraction(1, 9)]
        mu = sum(c*w**k for k, c in enumerate(coefficients))
        v = sum(k*c*w**(k-1) for k, c in enumerate(coefficients) if k)
        c3 = sum(k*(k-1)*c*w**(k-2) for k, c in enumerate(coefficients) if k > 1)
        big_l = mu/w**2
        first = v/w**2-2*mu/w**3
        second = c3/w**2-4*v/w**3+6*mu/w**4
        self.assertEqual(second, (w*w*c3-4*w*v+6*mu)/w**4)
        self.assertEqual(big_l*second-first*first,
                         (2*mu*mu+w*w*(mu*c3-v*v))/w**6)

    def test_scripts_pass_and_reject_optimized_python(self):
        for name in ('research/laplace_second_order.py',
                     'research/laplace_numeric_crosscheck.py'):
            bad = subprocess.run([sys.executable, '-O', str(ROOT/name)],
                                 cwd=ROOT, capture_output=True, text=True)
            self.assertNotEqual(bad.returncode, 0, name)
            self.assertIn('do not use python -O', bad.stderr, name)
        good = subprocess.run([sys.executable,
                               str(ROOT/'research/laplace_second_order.py')],
                              cwd=ROOT, capture_output=True, text=True)
        self.assertEqual(good.returncode, 0, good.stderr)
        self.assertIn('PASS', good.stdout)


if __name__ == '__main__':
    unittest.main()
