"""Finite-range consequences of a zero-free half-plane Re(s) > 7/8.

CONDITIONAL on an external input that this repository has NOT verified:

  E4  zeta(s) != 0 for Re(s) > 7/8.
      Source: "The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane
      Re(s)>7/8", OpenAI, 30 September 2026, Theorem 1.1, in the
      openai/math repository, whose formalization catalogue lists the Lean
      declaration OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re. That
      proof was not built or checked here.

together with E1 (Platt--Trudgian), E2 (Bellotti--Wong) and the five LMFDB
zero enclosures already used by zero_tail_certificate.py. See
research/notes/quasi-rh-consequences.txt for the derivations.

What is asserted, with outward-rounded Decimal intervals:

  (a) [E1, E2, five zeros, E4]  g(t) < 0 for 40 <= t <= 58.
      With the existing certificates this gives g(t) < 0 on 0 < t <= 58.
  (b) [E1, E2 only]             J(x) < 0 for 1 < x <= e^62.
  (c) [E1, E2, E4]              J(x) < 0 for 1 < x <= e^83.

J is the weighted Chebyshev-error integral of notes/chebyshev-error.txt.
Parts (b) and (c) use the one-sided bound g(t) <= A(H) (e^(b t) + 1), with
b = 1/2 unconditionally and b = 3/8 under E4.

FINITE RANGES ONLY. Nothing here is a proof of RH, and E4 itself does not
imply RH.

Run from any directory:  python3 research/zero_tail_seven_eighths.py
"""
from decimal import Decimal as D
from fractions import Fraction
from pathlib import Path
import sys

if not __debug__:
    raise RuntimeError('Certificate checks require assertions; do not use python -O.')

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parent))
from ns_startup_certificate import I, atan
from zero_tail_certificate import cosine
from laplace_second_order import tail_inverse_square_sum
# Importing screw_interval raises the global Decimal precision to 70. The
# interval class used here sets its own precision per operation, and the
# dyadic cell endpoints stay exact, so this has no effect on soundness.
import screw_interval

RAW_ZEROS = ['14.13472514173469379045725198',
             '21.02203963877155499262847959',
             '25.01085758014568876321379099',
             '30.42487612585951321031189753',
             '32.93506158773918969066236896']
TAIL_CONSTANT = '2.959408e-12'     # upper bound for A(H), as in zero-tail.txt
OFFSET = Fraction(3, 8)            # max |Re rho - 1/2| under E4
RANGE = (D(40), D(58))             # part (a)
J_LIMIT_UNCONDITIONAL = 62         # part (b): t = log x
J_LIMIT_SEVEN_EIGHTHS = 83         # part (c)


def exponent_times(offset, t):
    """Interval for offset*t with offset an exact Fraction."""
    return t*offset.numerator/offset.denominator


def cell_margin(pi, zeros, offset, a, b, tail_constant):
    """Interval for D_5(c) - L r - (exp(offset*b)+1)*tail_constant on [a, b].

    c is the midpoint, r the half-width, L = 2 sum 1/tau_j the Lipschitz
    constant of D_5. For every t in [a, b]: D_5(t) >= D_5(c) - L r, and the
    increasing envelope is at most its value at the RIGHT end b. A positive
    lower end therefore certifies D_5(t) > envelope(t) on the whole cell.
    """
    lipschitz = sum((2/z for z in zeros), I(0))
    midpoint = (I(a)+I(b))/2
    radius = (I(b)-I(a))/2
    deficit = sum((2*(1-cosine(z*midpoint, pi))/(z*z) for z in zeros), I(0))
    tail = exponent_times(offset, I(b)).exp()+1
    return deficit-lipschitz*radius-tail*I(tail_constant)


def certify_range(pi, zeros, offset, start, end, tail_constant):
    """Certify D_5(t) > (exp(offset*t)+1)*tail_constant on [start, end].

    Same Lipschitz-cell method as zero_tail_certificate.py; only the growth
    exponent of the tail envelope differs. Returns the accepted cells as
    (left, right, certified margin), in the order accepted, and the number
    of attempts.
    """
    stack = [(start, end)]
    accepted, attempts = [], 0
    while stack:
        a, b = stack.pop()
        margin = cell_margin(pi, zeros, offset, a, b, tail_constant)
        attempts += 1
        if margin.lo > 0:
            accepted.append((a, b, margin.lo))
        else:
            assert b-a > D('1e-8'), (a, b, margin)
            m = (a+b)/2            # dyadic refinement, exact in Decimal
            assert a < m < b
            stack.append((m, b))
            stack.append((a, m))
    return accepted, attempts


def j_margin(c_low, offset, t, tail_constant):
    """Lower bound for (C-1) t - 9/25 - A (exp(offset t) + 1).

    K = sum_{k>=1} 1/(4 (k+1/4)^2) <= (1/4)(16/25 + 4/5) = 9/25, comparing
    the sum with its first term plus an integral.
    """
    envelope = (exponent_times(offset, t).exp()+1)*I(tail_constant)
    return (I(c_low)-1)*t-I('0.36')-envelope


def main():
    pi = 16*atan(I(1)/5)-4*atan(I(1)/239)
    tail_mass = 2*tail_inverse_square_sum(pi)
    assert tail_mass.hi < D(TAIL_CONSTANT)
    zeros = [I(z)+I('-1e-26', '1e-26') for z in RAW_ZEROS]

    # (a) the extended sign certificate under E4.
    accepted, attempts = certify_range(
        pi, zeros, OFFSET, RANGE[0], RANGE[1], TAIL_CONSTANT)
    # The accepted cells tile [40, 58] with no gap.
    ordered = sorted(accepted)
    assert ordered[0][0] == RANGE[0] and ordered[-1][1] == RANGE[1]
    assert all(left[1] == right[0] for left, right in zip(ordered, ordered[1:]))
    cells = len(accepted)
    margin = min(cell[2] for cell in accepted)
    width = min(cell[1]-cell[0] for cell in accepted)

    # Without E4 the same five-zero method cannot reach t = 58: the deficit
    # never exceeds 4 sum 1/tau_j^2, which the b = 1/2 envelope dwarfs.
    ceiling = sum((4/(z*z) for z in zeros), I(0))
    half = (exponent_times(Fraction(1, 2), I(RANGE[1])).exp()+1)*I(TAIL_CONSTANT)
    assert ceiling.hi < half.lo

    # (b), (c): J(x) < 0. h(t) = (C-1) t - 9/25 - A (e^(b t) + 1) is concave
    # in t, so positivity at t = log 2 and at the right end covers the
    # whole interval; 1 < x <= 2 is the elementary case of the note.
    c_low = screw_interval.constants()[3].lo
    assert c_low > D('2.686')
    log_two = I(2).ln()
    margins = {}
    for name, offset, limit in (('1/2', Fraction(1, 2), J_LIMIT_UNCONDITIONAL),
                                ('3/8', OFFSET, J_LIMIT_SEVEN_EIGHTHS)):
        left = j_margin(c_low, offset, log_two, TAIL_CONSTANT)
        right = j_margin(c_low, offset, I(limit), TAIL_CONSTANT)
        assert left.lo > 0 and right.lo > 0, (name, left, right)
        margins[name] = (left.lo, right.lo)

    print('A(H) enclosure:', tail_mass)
    print('(a) accepted cells:', cells, 'attempts:', attempts)
    print('    smallest cell width:', width)
    print('    smallest certified positive margin:', margin)
    print('    five-zero ceiling vs b=1/2 envelope at t=58:',
          ceiling.hi, '<', half.lo)
    print('(b) J margins at t=log 2 and t=62, b=1/2:', *margins['1/2'])
    print('(c) J margins at t=log 2 and t=83, b=3/8:', *margins['3/8'])
    print('PASS: given E1, E2, five zeros AND UNVERIFIED INPUT E4:'
          ' g(t)<0 for 40<=t<=58; J(x)<0 for 1<x<=e^83.')
    print('PASS: given E1, E2 only: J(x)<0 for 1<x<=e^62.')
    print('Finite ranges only. Not a proof of RH.')


if __name__ == '__main__':
    main()
