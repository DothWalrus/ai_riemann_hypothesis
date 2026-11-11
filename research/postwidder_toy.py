"""Exploratory toy model for research/notes/post-widder-map.txt.

STATUS: exploratory computation with ordinary complex floats. It proves
nothing about zeta. It illustrates, on an artificial function whose "zeros"
we choose, the two rigorous statements of the note:

  * Detection threshold (Theorem D). A zero off the critical line at
    1/2 + b + i a forces sign violations of the normalised derivatives
        c_n(w) = (-1)^n w^(n+1) L^(n)(w) / n!
    for infinitely many n at every real w > w* := (a^2 + b^2)/(2 b).
  * Eventual positivity (Proposition E). For w < w*, c_n(w) tends to the
    positive constant M as n grows.
It also compares the first violation found with the heuristic order
estimate of the note's Section 6, which is not a theorem.

The toy function is the zero expansion of the note with the first five true
zeta ordinates on the line plus ONE artificial off-line quadruple:

    L_toy(w) = sum_gamma 2/[w (w^2 + gamma^2)],
    gamma in {tau_1..tau_5} and {a - i b, a + i b}.

For this L_toy the c_n(w) have the exact closed form (1.1) of
laplace-second-order.txt, evaluated here directly. No zeta data beyond the
five ordinates is used and no claim about the true xi is made.

The last block prints the same threshold for a HYPOTHETICAL zero of zeta just
above the verified height. That is arithmetic on the formula, not evidence
that such a zero exists.

Standard library only.  Run:  python3 research/postwidder_toy.py
"""
import cmath
import math

if not __debug__:
    raise RuntimeError('Checks require assertions; do not use python -O.')

ON_LINE = [14.134725141734694, 21.022039638771555, 25.010857580145689,
           30.424876125859513, 32.935061587739190]
TOY_HEIGHT = 40.0      # a: imaginary part of the artificial off-line zero
TOY_OFFSET = 0.4       # b: its distance from the critical line


def threshold(height, offset):
    """w* = |rho - 1/2|^2 / (2 (Re rho - 1/2))."""
    return (height*height+offset*offset)/(2*offset)


def limit_constant(height=TOY_HEIGHT, offset=TOY_OFFSET):
    """M_toy = residue of L_toy at w = 0 = sum over all gamma of 2/gamma^2."""
    off = 2*(2/complex(height, -offset)**2).real
    return sum(2/t**2 for t in ON_LINE)+off


def normalised_derivative(order, w, height=TOY_HEIGHT, offset=TOY_OFFSET):
    """c_n(w) for the toy function, from formula (1.1)."""
    power = order+1
    total = 0.0
    for tau in ON_LINE:
        # 1 - Re (1 - i tau/w)^-(n+1)
        z = cmath.exp(-power*cmath.log(complex(1, -tau/w)))
        total += 2/tau**2*(1-z.real)
    gamma = complex(height, -offset)
    plus = cmath.exp(-power*cmath.log(1+1j*gamma/w))
    minus = cmath.exp(-power*cmath.log(1-1j*gamma/w))
    # gamma and its conjugate contribute complex-conjugate terms.
    total += 2*((2/gamma**2)*(1-(plus+minus)/2)).real
    return total


def first_violation(w, max_order, height=TOY_HEIGHT, offset=TOY_OFFSET):
    """Smallest n <= max_order with c_n(w) < 0, or None."""
    for order in range(max_order+1):
        if normalised_derivative(order, w, height, offset) < 0:
            return order
    return None


def estimated_order(w, height, offset, main_term):
    """Heuristic order of the first forced violation (note, Section 6).

    The off-line pair's oscillating part of c_n(w) has modulus
    (2/|p|^2) (1 - 2b(w-w*)/w^2)^(-(n+1)/2) ~ (2/a^2) exp(b (n+1)(w-w*)/w^2),
    which must reach main_term. Only meaningful for w > w*.
    """
    w_star = threshold(height, offset)
    assert w > w_star
    need = math.log(main_term*height*height/2)
    return w*w*need/(offset*(w-w_star))


def main():
    w_star = threshold(TOY_HEIGHT, TOY_OFFSET)
    m_toy = limit_constant()
    print(f'toy off-line zero: 1/2 + {TOY_OFFSET} + {TOY_HEIGHT} i')
    print(f'detection threshold w* = {w_star:.2f},  M_toy = {m_toy:.6f}')
    print('   w/w*          w   first n with c_n<0   heuristic n'
          '   c_n at n = w^2')
    for ratio in (0.25, 0.5, 0.9, 0.99, 1.01, 1.1, 1.5, 2, 5, 20):
        w = ratio*w_star
        horizon = int(40*w)
        found = first_violation(w, horizon)
        where = '  none found' if found is None else f'{found:12d}'
        if ratio > 1:
            guess = estimated_order(w, TOY_HEIGHT, TOY_OFFSET, m_toy)
            predicted = f'{guess:12.3g}'
            limit = '            -'
        else:
            predicted = '           -'
            far = normalised_derivative(int(w*w), w)
            limit = f'{far: .6e}'
            # Proposition E: c_n(w) -> M_toy below the threshold.
            assert abs(far-m_toy) < 0.005*m_toy, (ratio, far, m_toy)
            # Observation about this toy, NOT implied by Proposition E:
            # no negative order among n <= 40 w.
            assert found is None
        print(f'{ratio:7.2f} {w:10.1f}   {where}  {predicted}   {limit}')
        if ratio >= 1.5:
            # Theorem D guarantees violations; for these ratios the scan
            # is long enough to reach the first, and the heuristic is
            # within a factor 1.5 of it.
            assert found is not None
            assert found <= guess <= 1.5*found, (ratio, found, guess)
    # The first violation is not visible at low order.
    assert first_violation(2*w_star, 2000) is None
    print('at w = 2 w*: no violation among the first 2000 orders.')

    height = 3.0e12
    print()
    print('HYPOTHETICAL zero of zeta just above the verified height 3e12')
    print('(arithmetic on the heuristic only; no such zero is known):')
    for offset in (0.5, 0.1, 0.01):
        w_star = threshold(height, offset)
        least = estimated_order(2*w_star, height, offset, 0.0462)
        print(f'  Re rho - 1/2 = {offset:5.2f}:  w* = {w_star:.2e},'
              f'  least order (at w = 2 w*) ~ {least:.1e}')
    print('DONE: exploratory toy model; not a statement about zeta.')


if __name__ == '__main__':
    main()
