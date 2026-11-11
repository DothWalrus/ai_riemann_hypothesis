"""Exploratory floating-point cross-check for research/notes/laplace-second-order.txt.

STATUS: exploratory computation. Ordinary float quadrature, no interval
arithmetic, no certified error bounds. It proves nothing. Its purpose is to
catch algebra, sign and normalisation mistakes in the written argument by
computing the same quantities in two unrelated ways and comparing them with
every inequality the note claims.

Route 1 (theta kernel).  xi(1/2+w) = integral_0^infinity A(u) cosh(w u) du
with the classical kernel A.  The tilted moments give

    mu = kappa'(w),  v = kappa''(w),  c3 = kappa'''(w),
    kappa(w) = log[xi(1/2+w)/xi(1/2)].

Route 2 (explicit formula, only for w >= 2.5).  With s = 1/2+w,

    kappa'(w) = 1/s + 1/(s-1) - log(pi)/2 + digamma(s/2)/2 + zeta'/zeta(s).

Neither route uses the location of any zeta zero.  The first zero ordinate
appears only inside the claimed lower bounds that are being tested.

Standard library only.  Run:  python3 research/laplace_numeric_crosscheck.py
"""
import math

if not __debug__:
    raise RuntimeError('Checks require assertions; do not use python -O.')

TAU1 = 14.134725141734694        # first zero ordinate, used only in bounds
SPLIT = 20.0                     # the note's boundary between its two regions


def kernel(u):
    """A(u) = sum_n (8 pi^2 n^4 e^(9u/2) - 12 pi n^2 e^(5u/2)) exp(-pi n^2 e^(2u))."""
    e2 = math.exp(2*u)
    total = 0.0
    for n in range(1, 40):
        decay = math.pi*n*n*e2
        if decay > 700:
            break
        total += ((8*math.pi**2*n**4*math.exp(4.5*u)
                   - 12*math.pi*n*n*math.exp(2.5*u))*math.exp(-decay))
    return total


STEP = 1.0/2048
UPPER = 3.0    # A(u) < exp(-pi e^6) < 1e-500 beyond this; keeps exp(w u) finite
NODES = [k*STEP for k in range(int(UPPER/STEP)+1)]
KERNEL = [kernel(u) for u in NODES]


def simpson(values):
    assert len(values) % 2 == 1
    total = values[0]+values[-1]
    total += 4*math.fsum(values[1:-1:2])+2*math.fsum(values[2:-1:2])
    return total*STEP/3


def cumulants(w):
    """Return (mu, v, c3) from tilted theta-kernel moments."""
    # Remove a common factor exp(w*shift) so large w does not overflow.
    shift = max(NODES, key=lambda u: (w*u-math.pi*math.exp(2*u)))
    plus = [math.exp(w*(u-shift)) for u in NODES]
    minus = [math.exp(-w*(u+shift)) for u in NODES]
    cosh = [(p+m)/2 for p, m in zip(plus, minus)]
    sinh = [(p-m)/2 for p, m in zip(plus, minus)]
    m0 = simpson([a*c for a, c in zip(KERNEL, cosh)])
    m1 = simpson([a*u*s for a, u, s in zip(KERNEL, NODES, sinh)])/m0
    m2 = simpson([a*u*u*c for a, u, c in zip(KERNEL, NODES, cosh)])/m0
    m3 = simpson([a*u**3*s for a, u, s in zip(KERNEL, NODES, sinh)])/m0
    return m1, m2-m1*m1, m3-3*m1*m2+2*m1**3


def digamma(x):
    shift = 0.0
    while x < 30:
        shift -= 1/x
        x += 1
    inv = 1/(x*x)
    return (shift+math.log(x)-1/(2*x)
            - inv*(1/12-inv*(1/120-inv*(1/252-inv/240))))


def primes(limit):
    sieve = bytearray(b'\1')*(limit+1)
    sieve[:2] = b'\0\0'
    for p in range(2, math.isqrt(limit)+1):
        if sieve[p]:
            sieve[p*p::p] = b'\0'*len(sieve[p*p::p])
    return [p for p in range(limit+1) if sieve[p]]


PRIMES = primes(200000)


def mu_explicit(w):
    """kappa'(w) from the explicit formula; requires w >= 2.5."""
    s = w+0.5
    assert s >= 3
    zeta_part = -math.fsum(math.log(p)/(p**s-1) for p in PRIMES
                           if s*math.log(p) < 700)
    return 1/s+1/(s-1)-math.log(math.pi)/2+digamma(s/2)/2+zeta_part


def main():
    xi_half = simpson(KERNEL)
    second = simpson([a*u*u for a, u in zip(KERNEL, NODES)])/xi_half
    print(f'xi(1/2)      = {xi_half:.12f}  (literature 0.497120778188...)')
    print(f"xi''/xi(1/2) = {second:.12f}  (repository note 0.04620998623...)")
    assert abs(xi_half-0.4971207781883) < 1e-10
    assert abs(second-0.04620998623084) < 1e-10

    samples = ([0.01, 0.05, 0.1, 0.25, 0.5, 1, 2, 3, 5, 8, 10, 12, 14, 16,
                17, 18, 19, 20, 22, 25, 30, 40, 60, 80, 100, 150, 200]
               + [k/4 for k in range(1, 81)])
    worst = {'L2': math.inf, 'D': math.inf, 'B1': math.inf, 'B2': math.inf,
             'explicit': 0.0}
    print('     w        mu           v            c3'
          '        w^2c3-4wv+6mu   2mu^2+w^2(mu c3-v^2)')
    for w in sorted(set(samples)):
        mu, v, c3 = cumulants(w)
        n1 = w*w*c3-4*w*v+6*mu           # = w^4 L''
        n2 = 2*mu*mu+w*w*(mu*c3-v*v)     # = w^6 (L L'' - L'^2)
        if w in (0.01, 0.5, 1, 5, 10, 14, 17, 20, 30, 60, 100, 200):
            print(f'{w:7.2f} {mu:12.8f} {v:12.8f} {c3:13.9f}'
                  f' {n1:14.8f} {n2:18.10f}')
        # Signs already justified in the repository notes.
        assert mu > 0 and v > 0 and c3 <= 1e-12 and w*v <= mu*(1+1e-9)
        # The two target inequalities.
        assert n1 > 0 and n2 > 0, w
        # Lemma A of the note: orders n = 0, 1, 2 of
        #   (-1)^n L^(n) >= (2 n!/(tau1^2 w^(n+1)))
        #                   * [1-(1+tau1^2/w^2)^(-(n+1)/2)]   (tail ignored).
        scaled = [mu/w, (2*mu-w*v)/w, n1/(2*w)]   # (-1)^n L^(n) w^(n+1)/n!
        for order, value in enumerate(scaled):
            bound = 2/TAU1**2*(1-(1+TAU1**2/(w*w))**(-(order+1)/2))
            assert value >= bound*(1-1e-7), (w, order, value, bound)
        worst['L2'] = min(worst['L2'], scaled[2]*2/(4/(w*w+TAU1**2)))
        # Lemma C: w^4 (L L'' - L'^2) >= 3/(w^2+tau1^2)^2 (tail ignored).
        hankel_bound = 3/(w*w+TAU1**2)**2
        assert n2/(w*w) >= hankel_bound*(1-1e-7), (w, n2/(w*w), hankel_bound)
        worst['D'] = min(worst['D'], n2/(w*w)/hankel_bound)
        if w >= SPLIT:
            s = w+0.5
            floor = math.log(s/(2*math.pi))/2
            # Lemma B ingredients.
            assert mu >= floor
            assert v <= 1/(2*s)
            assert c3 >= -1/(2*s*s)
            first = 3*math.log(w/(2*math.pi))-2.5
            half = math.log(w/(2*math.pi))/2
            second_bound = 2*half*half-half/2-0.25
            assert first > 0 and second_bound > 0
            assert n1 >= first and n2 >= second_bound
            worst['B1'] = min(worst['B1'], n1-first)
            worst['B2'] = min(worst['B2'], n2-second_bound)
        if w >= 2.5:
            difference = abs(mu-mu_explicit(w))
            worst['explicit'] = max(worst['explicit'], difference)
            assert difference < 1e-8, (w, mu, mu_explicit(w))
    print('least ratio  w^3 L\'\' / [4/(w^2+tau1^2)]            :',
          f"{worst['L2']:.4f}")
    print('least ratio  w^4 (L L\'\'-L\'^2) / [3/(w^2+tau1^2)^2]  :',
          f"{worst['D']:.4f}")
    print('least slack over the Lemma B bounds (w >= 20)      :',
          f"{worst['B1']:.4f}, {worst['B2']:.4f}")
    print('largest |theta-kernel mu - explicit-formula mu|    :',
          f"{worst['explicit']:.2e}")
    print('CONSISTENT: every sampled inequality of the note holds.'
          ' Exploratory floats only; this is not a proof.')


if __name__ == '__main__':
    main()
