"""Elementary interval certificate for g_zeta(t)<0, 0<t<=log(2).

Uses only Python's standard library. Decimal exp/ln are correctly rounded;
one ulp is added at both endpoints to enclose their exact values. All other
operations use directed rounding. The proof using these bounds is in
ns_startup_lemma.md. This is finite-interval evidence, not an RH proof.
"""

from decimal import Decimal as D, localcontext, ROUND_FLOOR, ROUND_CEILING

if not __debug__:
    raise RuntimeError('Certificate checks require assertions; do not use python -O.')

PREC = 60


def rounded(fn, mode):
    with localcontext() as c:
        c.prec = PREC
        c.rounding = mode
        return fn()


class I:
    def __init__(self, lo, hi=None):
        self.lo, self.hi = D(lo), D(lo if hi is None else hi)
        assert self.lo <= self.hi

    def __add__(self, other):
        other = wrap(other)
        return I(rounded(lambda: self.lo + other.lo, ROUND_FLOOR),
                 rounded(lambda: self.hi + other.hi, ROUND_CEILING))

    __radd__ = __add__

    def __neg__(self):
        return I(self.hi.copy_negate(), self.lo.copy_negate())

    def __sub__(self, other):
        return self + -wrap(other)

    def __rsub__(self, other):
        return wrap(other) + -self

    def __mul__(self, other):
        other = wrap(other)
        pairs = [(a, b) for a in (self.lo, self.hi)
                 for b in (other.lo, other.hi)]
        return I(min(rounded(lambda: a*b, ROUND_FLOOR) for a, b in pairs),
                 max(rounded(lambda: a*b, ROUND_CEILING) for a, b in pairs))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = wrap(other)
        assert other.lo > 0 or other.hi < 0
        inv = I(rounded(lambda: D(1)/other.hi, ROUND_FLOOR),
                rounded(lambda: D(1)/other.lo, ROUND_CEILING))
        return self * inv

    def __rtruediv__(self, other):
        return wrap(other) / self

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        result = I(1)
        for _ in range(n):
            result = result * self
        return result

    def elementary(self, name):
        # Python Decimal.exp/ln always correctly round to nearest.
        vals = []
        for x in (self.lo, self.hi):
            y = rounded(lambda: getattr(x, name)(), ROUND_FLOOR)
            ulp = D(1).scaleb(y.adjusted() - PREC + 1)
            vals.append((rounded(lambda: y-ulp, ROUND_FLOOR),
                         rounded(lambda: y+ulp, ROUND_CEILING)))
        return I(vals[0][0], vals[1][1])

    def exp(self):
        return self.elementary('exp')

    def ln(self):
        return self.elementary('ln')

    def __repr__(self):
        return f'[{self.lo}, {self.hi}]'


def wrap(x):
    return x if isinstance(x, I) else I(x)


def atan(x, terms=300):
    assert x.lo >= 0 and x.hi < 1
    s, power, square = I(0), x, x*x
    for n in range(terms):
        term = power/(2*n+1)
        s = s + (term if n % 2 == 0 else -term)
        power = power*square
    err = (power/(2*terms+1)).hi
    return s + I(err.copy_negate(), err)


def atanh(x, terms=300):
    assert x.lo >= 0 and x.hi < 1
    s, power, square = I(0), x, x*x
    for n in range(terms):
        s = s + power/(2*n+1)
        power = power*square
    err = (power/((2*terms+1)*(1-square))).hi
    return s + I(0, err)


def main():
    pi = 16*atan(I(1)/5) - 4*atan(I(1)/239)
    # Euler--Maclaurin: H_N-log N-1/(2N)+1/(12N^2)
    # encloses gamma between itself minus 1/(120N^4) and itself.
    n = 1000
    harmonic = sum((I(1)/k for k in range(1, n+1)), I(0))
    gamma_upper = harmonic-I(n).ln()-I(1)/(2*n)+I(1)/(12*n*n)
    gamma = gamma_upper + I((I(1)/(120*n**4)).hi.copy_negate(), 0)
    C = (gamma+pi/2+3*I(2).ln()+pi.ln())/2
    quarter = I(1)/4
    h_upper = -4*(quarter.exp()-1)+C/2
    for k in range(1, 17):
        a = k+quarter
        h_upper = h_upper-(1-(-a).exp())/(4*a*a)
    x = (-quarter).exp()
    derivative = -2*(quarter.exp()-x)+C-atanh(x)-atan(x)
    left = quarter.exp()
    right = (I(1)/3).exp()
    left_poly = left**3-left-1
    right_poly = right**3-right-1
    assert left_poly.hi < 0 < right_poly.lo
    assert h_upper.hi < D('-0.025')
    assert derivative.lo > D('-0.03125') and derivative.hi < 0
    assert I(2).ln().lo > D('0.5')
    print('gamma:', gamma)
    print('C:', C)
    print('H(1/2) upper bound from 16 terms:', h_upper)
    print("H'(1/2):", derivative)
    print('P(exp(1/4)):', left_poly)
    print('P(exp(1/3)):', right_poly)
    print('PASS: H(1/2)<-1/40, -1/32<H\'(1/2)<0, 1/4<t*<1/3.')


if __name__ == '__main__':
    main()
