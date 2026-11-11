"""Certify g_zeta(t)<0 on [1/2,40] using five real zeros and a tail.

Primary external inputs and analytic bounds are documented in
research/notes/zero-tail.txt and research/lmfdb_first_five_source.txt.
No zeta evaluation is performed. Uses the interval arithmetic of the
startup certificate. Run from any directory with Python 3.
"""

from decimal import Decimal as D
from math import factorial
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from ns_startup_certificate import I, atan

if not __debug__:
    raise RuntimeError('Certificate checks require assertions; do not use python -O.')


def cosine(angle, pi):
    # The integer reduction need not be exact: the enclosure and the
    # |reduced argument|<=4 assertion suffice for the Taylor remainder.
    k = round(float(angle.lo)/(2*float(pi.lo)))
    y = angle-2*k*pi
    assert y.lo >= -4 and y.hi <= 4
    square = y*y
    term, total = I(1), I(1)
    for n in range(1, 31):
        term = -term*square/((2*n-1)*(2*n))
        total = total+term
    err = (I(4)**62/factorial(62)).hi
    return total+I(err.copy_negate(), err)


def main():
    pi = 16*atan(I(1)/5)-4*atan(I(1)/239)
    height = I(3000000000000)
    logh = height.ln()
    r = I('.112')*logh+I('.12567')*logh.ln()+I('3.77417')
    tail_mass = ((height/(2*pi)).ln()+1)/(pi*height)
    tail_mass = tail_mass+(4*r+I('.112')+I('.12567')/logh)/(height*height)
    assert tail_mass.hi < D('2.959408e-12')
    # LMFDB printed values have error < 2.5e-31; radius 1e-26
    # also includes the digits discarded here.
    raw = ['14.13472514173469379045725198',
           '21.02203963877155499262847959',
           '25.01085758014568876321379099',
           '30.42487612585951321031189753',
           '32.93506158773918969066236896']
    zeros = [I(z)+I('-1e-26', '1e-26') for z in raw]
    lipschitz = sum((2/z for z in zeros), I(0))
    stack = [(D('.5'), D(40))]
    cells, attempts = 0, 0
    minimum_margin = D('Infinity')
    largest_width = D(0)
    smallest_width = D('Infinity')
    while stack:
        a, b = stack.pop()
        midpoint = (I(a)+I(b))/2
        radius = (I(b)-I(a))/2
        deficit = sum((2*(1-cosine(z*midpoint, pi))/(z*z)
                       for z in zeros), I(0))
        tail = (I(b)/2).exp()+1
        margin = deficit-lipschitz*radius-tail*I('2.959408e-12')
        attempts += 1
        if margin.lo > 0:
            cells += 1
            minimum_margin = min(minimum_margin, margin.lo)
            width = b-a
            largest_width = max(largest_width, width)
            smallest_width = min(smallest_width, width)
        else:
            assert b-a > D('1e-8'), (a, b, margin)
            # Dyadic endpoints here have fewer than 28 significant
            # digits, so the default Decimal context computes exactly.
            m = (a+b)/2
            assert a < m < b
            stack.append((m, b))
            stack.append((a, m))
    print('Tail mass enclosure:', tail_mass)
    print('Deficit Lipschitz enclosure:', lipschitz)
    print('Accepted cells:', cells, 'Total attempts:', attempts)
    print('Smallest/largest cell width:', smallest_width, largest_width)
    print('Smallest certified positive margin:', minimum_margin)
    print('PASS: g_zeta(t)<0 for 1/2<=t<=40.')


if __name__ == '__main__':
    main()
