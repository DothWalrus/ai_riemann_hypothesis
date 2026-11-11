"""Finite anchored Gram tests using prime-side interval values only.

An interval LDL decomposition with positive pivots proves these specified
finite matrices positive definite. It says nothing about all point sets.
"""
from fractions import Fraction
from itertools import combinations
import json
try:
    from .screw_interval import I, Screw, prime_powers
except ImportError:  # Direct execution as python research/kernel_control.py.
    from screw_interval import I, Screw, prime_powers


def checked_values(screw, points):
    assert all(0 < p <= 4 for p in points)
    assert I(55).ln().lo > 4
    values = {Fraction(0): I(0)}
    for t in sorted(set(abs(s-t) for s in [Fraction(0)]+points
                        for t in [Fraction(0)]+points)):
        if not t:
            continue
        tt = I(t)
        a, b = I(0), I(0)
        # e^4<55; all points and differences below are <=4.
        for q, p in prime_powers(55):
            event = I(q).ln()
            if event.hi < tt.lo:
                w = I(p).ln()/I(q).sqrt()
                a += w
                b += w*event
            elif event.lo <= tt.hi:
                raise AssertionError('Choose control points away from events')
        values[t] = screw.value(tt, a, b)
    return values


def pivots(matrix):
    n = len(matrix)
    lower = [[I(0) for _ in range(n)] for _ in range(n)]
    d = []
    for j in range(n):
        pivot = matrix[j][j]-sum((lower[j][k].square()*d[k]
                                 for k in range(j)), I(0))
        assert pivot.lo > 0, (j, pivot.strings())
        d.append(pivot)
        lower[j][j] = I(1)
        for i in range(j+1, n):
            numerator = matrix[i][j]-sum((lower[i][k]*lower[j][k]*d[k]
                                         for k in range(j)), I(0))
            lower[i][j] = numerator/pivot
    return d


def run():
    screw = Screw()
    points = [Fraction(i, 2) for i in range(1, 9)]
    values = checked_values(screw, points)
    matrix = [[values[abs(s-t)]-values[s]-values[t] for t in points]
              for s in points]
    d = pivots(matrix)
    # Separately check every 2x2 principal minor, including widely
    # separated points. This can catch an indexing/sign regression.
    minors = []
    for i, j in combinations(range(len(points)), 2):
        determinant = matrix[i][i]*matrix[j][j]-matrix[i][j].square()
        assert determinant.lo > 0
        minors.append(determinant.lo)
    return {'scope': 'finite control only, not a proof of RH',
            'points': [str(p) for p in points],
            'kernel': 'K(s,t)=g(s-t)-g(s)-g(t)',
            'LDL_pivot_enclosures': [p.strings() for p in d],
            'two_by_two_minors_checked': len(minors),
            'least_minor_lower_bound': str(min(minors)),
            'external_zero_data_used': False}


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
