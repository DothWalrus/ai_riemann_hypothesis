"""Finite-range control for Nakamura--Suzuki (2023), formula (1.5).

Uses Python Decimal with outward enclosures, exact rational series for pi
and Catalan, and the classical positive-real Euler--Maclaurin remainder
bound for the digamma function. No zero locations or RH are assumed.
This verifies a FINITE interval only; it is not a proof of RH.

Decimal exp/ln/sqrt are correctly rounded to nearest; we expand each result
by one representable number on both sides, rather than assuming their
rounding-mode argument gives a directed transcendental result.
"""
from decimal import Context, Decimal, ROUND_CEILING, ROUND_FLOOR, getcontext
from fractions import Fraction
import argparse
import json
import math

if not __debug__:
    raise RuntimeError('Certificate checks require assertions; do not use python -O.')

PREC = 70
getcontext().prec = PREC
DOWN = Context(prec=PREC, rounding=ROUND_FLOOR)
UP = Context(prec=PREC, rounding=ROUND_CEILING)
NEAR = Context(prec=PREC)


def dec_pair(x):
    if isinstance(x, Fraction):
        a, b = Decimal(x.numerator), Decimal(x.denominator)
        return DOWN.divide(a, b), UP.divide(a, b)
    x = Decimal(str(x))
    return x, x


class I:
    def __init__(self, lo=0, hi=None):
        if isinstance(lo, I):
            self.lo, self.hi = lo.lo, lo.hi
        elif hi is None:
            self.lo, self.hi = dec_pair(lo)
        else:
            self.lo, self.hi = Decimal(str(lo)), Decimal(str(hi))
        assert self.lo <= self.hi

    def __add__(self, other):
        other = I(other)
        return I(DOWN.add(self.lo, other.lo), UP.add(self.hi, other.hi))

    __radd__ = __add__

    def __neg__(self):
        return I(self.hi.copy_negate(), self.lo.copy_negate())

    def __sub__(self, other):
        return self + (-I(other))

    def __rsub__(self, other):
        return I(other) - self

    def __mul__(self, other):
        other = I(other)
        pairs = [(a, b) for a in (self.lo, self.hi)
                 for b in (other.lo, other.hi)]
        return I(min(DOWN.multiply(a, b) for a, b in pairs),
                 max(UP.multiply(a, b) for a, b in pairs))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = I(other)
        assert not (other.lo <= 0 <= other.hi)
        inv = I(DOWN.divide(Decimal(1), other.hi),
                UP.divide(Decimal(1), other.lo))
        return self * inv

    def __rtruediv__(self, other):
        return I(other) / self

    def square(self):
        if self.lo <= 0 <= self.hi:
            return I(0, max(UP.multiply(self.lo, self.lo),
                            UP.multiply(self.hi, self.hi)))
        return self * self

    def exp(self):
        return I(NEAR.next_minus(NEAR.exp(self.lo)),
                 NEAR.next_plus(NEAR.exp(self.hi)))

    def ln(self):
        assert self.lo > 0
        return I(NEAR.next_minus(NEAR.ln(self.lo)),
                 NEAR.next_plus(NEAR.ln(self.hi)))

    def sqrt(self):
        assert self.lo >= 0
        low = NEAR.sqrt(self.lo)
        return I(0 if self.lo == 0 else NEAR.next_minus(low),
                 NEAR.next_plus(NEAR.sqrt(self.hi)))

    def midpoint(self):
        return NEAR.divide(NEAR.add(self.lo, self.hi), Decimal(2))

    def strings(self):
        return [str(self.lo), str(self.hi)]


def arctan_recip(q, terms=110):
    s = sum((Fraction((-1)**k, (2*k+1)*q**(2*k+1))
             for k in range(terms)), Fraction(0))
    err = Fraction(1, (2*terms+1)*q**(2*terms+1))
    # Symmetric error bound is conservative for an alternating series.
    return I(s) + I(-I(err).hi, I(err).hi)


def bernoulli(n):
    a = [Fraction(0) for _ in range(n+1)]
    for m in range(n+1):
        a[m] = Fraction(1, m+1)
        for j in range(m, 0, -1):
            a[j-1] = j * (a[j-1] - a[j])
    return a[0]


def constants():
    pi = 16*arctan_recip(5) - 4*arctan_recip(239)
    n, order = 128, 16
    harmonic = sum((Fraction(1, j) for j in range(1, n+1)), Fraction(0))
    rational = harmonic - Fraction(1, 2*n)
    for k in range(1, order+1):
        rational += bernoulli(2*k) / (2*k*n**(2*k))
    remainder = abs(bernoulli(2*order+2) /
                    ((2*order+2)*n**(2*order+2)))
    radius = I(remainder).hi
    euler = I(rational) - I(n).ln() + I(-radius, radius)
    # Euler transformation of G=sum (-1)^n/(2n+1)^2.
    # d_k = int_0^1 (1-x^2)^k*(-log x) dx lies in [0,1].
    # G=sum d_k/2^(k+1); the tail after terms terms is <=2^-terms.
    terms = 240
    diffs = [Fraction(1, (2*j+1)**2) for j in range(terms)]
    total = Fraction(0)
    for k in range(terms):
        assert 0 < diffs[0] <= 1
        total += diffs[0] / 2**(k+1)
        diffs = [diffs[j]-diffs[j+1] for j in range(len(diffs)-1)]
    catalan = I(total) + I(0, I(Fraction(1, 2**terms)).hi)
    c = (euler + pi/2 + 3*I(2).ln() + pi.ln())/2
    phi_one = pi.square() + 8*catalan
    return pi, euler, catalan, c, phi_one


class Screw:
    def __init__(self):
        self.pi, self.euler, self.catalan, self.c, self.phi_one = constants()

    def smooth(self, t, derivative=False):
        t = I(t)
        assert t.lo >= Decimal('0.49')
        z = (-2*t).exp()
        prefactor = (-t/2).exp()
        sums = I(0)
        power = I(1)
        for k in range(200):
            denominator = I(Fraction(4*k+1, 4))
            sums += power / (denominator if derivative else denominator.square())
            power *= z
        denominator = I(Fraction(4*200+1, 4))
        tail = (prefactor*power /
                ((denominator if derivative else denominator.square())*(1-z)))
        series = prefactor*sums + I(0, tail.hi)
        p, m = (t/2).exp(), prefactor
        if derivative:
            return -2*(p-m) + self.c - series/2
        return -4*(p+m-2) + self.c*t + (series-self.phi_one)/4

    def value(self, t, active_a, active_b):
        return self.smooth(t) + active_a*I(t) - active_b

    def slope(self, t, active_a):
        return self.smooth(t, derivative=True) + active_a


def prime_powers(limit):
    prime = bytearray(b'\1')*(limit+1)
    prime[:2] = b'\0\0'
    for p in range(2, math.isqrt(limit)+1):
        if prime[p]:
            prime[p*p:limit+1:p] = b'\0'*(((limit-p*p)//p)+1)
    events = []
    for p in range(2, limit+1):
        if prime[p]:
            q = p
            while q <= limit:
                events.append((q, p))
                q *= p
    return sorted(events)


def gap_max(screw, left, right, a, b):
    # g''<0 throughout [1/2,infty) away from event atoms. The fixed
    # active branch has this smooth curvature even if extended slightly
    # beyond interval-enclosed endpoints. Thus each maximum is either an
    # endpoint or the unique stationary point.
    if screw.slope(left, a).hi < 0:
        location, kind = left, 'left'
    elif screw.slope(right, a).lo > 0:
        location, kind = right, 'right'
    else:
        lo, hi = left.lo, right.hi
        for _ in range(52):
            mid = NEAR.divide(NEAR.add(lo, hi), Decimal(2))
            d = screw.slope(I(mid), a)
            if d.lo > 0:
                lo = mid
            elif d.hi < 0:
                hi = mid
            else:
                break
        location, kind = I(lo, hi), 'stationary_bracket'
    return screw.value(location, a, b), location, kind


def run(limit):
    screw = Screw()
    half_value = screw.smooth(I('0.5'))
    half_slope = screw.smooth(I('0.5'), derivative=True)
    assert half_value.hi < -Decimal(1)/40
    assert -Decimal(1)/32 < half_slope.lo < half_slope.hi < 0
    a, b, left, previous_q = I(0), I(0), I('0.5'), 'start'
    records = []
    for q, p in prime_powers(limit):
        right = I(q).ln()
        upper, location, kind = gap_max(screw, left, right, a, b)
        assert upper.hi < 0, (q, upper.strings())
        records.append({'after': previous_q, 'through': q,
                        'candidate_value_enclosure': upper.strings(),
                        'gap_max_upper_bound': str(upper.hi),
                        'location': location.strings(), 'type': kind})
        weight = I(p).ln()/I(q).sqrt()
        a += weight
        b += weight*right
        left, previous_q = right, q
    if previous_q != limit:
        upper, location, kind = gap_max(screw, left, I(limit).ln(), a, b)
        assert upper.hi < 0
        records.append({'after': previous_q, 'through': limit,
                        'candidate_value_enclosure': upper.strings(),
                        'gap_max_upper_bound': str(upper.hi),
                        'location': location.strings(), 'type': kind})
    weakest = max(records, key=lambda r: Decimal(r['gap_max_upper_bound']))
    return {'function': 'Nakamura-Suzuki g, formula 1.5, 2023',
            'claim': 'finite-range sign verification only, not RH',
            'precision_decimal': PREC, 'prime_limit': limit,
            'range_checked': '[1/2, log(prime_limit)]',
            'startup_value': half_value.strings(),
            'startup_slope': half_slope.strings(),
            'constants': {'pi': screw.pi.strings(),
                          'euler_gamma': screw.euler.strings(),
                          'catalan': screw.catalan.strings()},
            'gap_count': len(records), 'weakest_gap': weakest,
            'gaps': records}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--limit', type=int, default=100)
    args = parser.parse_args()
    assert 2 <= args.limit <= 100000
    print(json.dumps(run(args.limit), indent=2))
