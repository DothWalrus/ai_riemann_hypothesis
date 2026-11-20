"""Finite diagnostic for a proposed positive factorial-floor decomposition.

This is a finite interval calculation, not a proof of RH. The separate Lean
file independently certifies the floor-table identity and actual kernel-weight
bounds using proved logarithm series; it does not import Decimal output.
"""

from math import isqrt
from pathlib import Path
import sys

if not __debug__:
    raise RuntimeError('Interval checks require assertions; do not use python -O.')

if __package__ in (None, ''):
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from ns_startup_certificate import I, D


SUPPORT = (2, 3, 5, 8, 9, 13)
SIGNS = (1, -1, -1, -1, 1, 1)


def sqrt_interval(n):
    """Enclose sqrt(n) by integer square comparisons, without float/sqrt."""
    assert isinstance(n, int) and n > 0
    scale = 10 ** 30
    root = isqrt(n * scale * scale)
    assert root * root <= n * scale * scale < (root + 1) * (root + 1)
    return I(root, root + 1) / scale


def main():
    dual = []
    for m in range(17):
        column = sum(sign * (m // d) for sign, d in zip(SIGNS, SUPPORT))
        expected = (1 if m in (2, 4, 13) else 2 if m == 14 else 0)
        assert column == expected
        dual.append(column)
    values = {d: (I(16) / d).ln() / sqrt_interval(d) for d in SUPPORT}
    assert values[2].hi <= D('1.471')
    assert values[3].lo >= D('0.966')
    assert values[5].lo >= D('0.520')
    assert values[8].lo >= D('0.245')
    assert values[9].hi <= D('0.192')
    assert values[13].hi <= D('0.058')
    result = sum((sign * values[d] for sign, d in zip(SIGNS, SUPPORT)), I(0))
    assert result.hi < D('-0.01')
    print('Dual floor-table columns m=0,...,16:', dual)
    for d in SUPPORT:
        print(f'w({d}) = log(16/{d})/sqrt({d}):', values[d])
    print('w(2)-w(3)-w(5)-w(8)+w(9)+w(13):', result)
    print('PASS: finite floor-table identity and outward interval upper bound < -1/100.')
    print('Scope: diagnostic obstruction to a positive coefficient representation, not an RH result.')


if __name__ == '__main__':
    main()
