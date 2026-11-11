"""Interval check of the constants used in notes/laplace-second-order.txt.

The note proves, for L(w) = kappa'(w)/w^2 with
kappa(w) = log[xi(1/2+w)/xi(1/2)]:

    L''(w) > 0   and   L(w) L''(w) - L'(w)^2 > 0   for every real w > 0,

from published zero verification, a published zero-counting bound, and
elementary estimates. THIS IS NOT A PROOF OF RH and not a step that brings
the complete-monotonicity programme closer to one; see the note's Section 7.

This script does not evaluate zeta, xi or L. The argument is analytic; the
only numerical content is a handful of inequalities between explicit
constants, asserted here with the outward-rounded Decimal intervals of
ns_startup_certificate.py. The external inputs are hypotheses of the note:

  E1  every zero rho of zeta with 0 < |Im rho| <= H = 3*10^12 has
      Re rho = 1/2                                   (Platt--Trudgian 2021);
  E2  |N(T) - T/(2 pi) log(T/(2 pi e))| <= R(T) for T >= e, where
      R(T) = .11200 log T + .12567 loglog T + 3.77417
                                                  (Bellotti--Wong, Thm 1.1);
  E3  the least positive zero ordinate tau_1 satisfies 14.13 < tau_1 < 14.14
      and there is no zero with 0 < Im rho < 14      (LMFDB / Platt data).

Run from any directory:  python3 research/laplace_second_order.py
"""
from decimal import Decimal as D
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from ns_startup_certificate import I, atan

if not __debug__:
    raise RuntimeError('Certificate checks require assertions; do not use python -O.')

HEIGHT = 3000000000000                 # E1
TAU1 = ('14.13', '14.14')              # E3, deliberately wide
SPLIT = 20                             # boundary W between Lemmas A/C and B
WIDE = 100000                          # larger range certified for Lemma A


def tail_inverse_square_sum(pi):
    """Upper bound for T2 = sum over zeros with Im rho > H of 1/(Im rho)^2.

    Same Stieltjes estimate as research/notes/zero-tail.txt, formula (1);
    that note bounds A(H) <= 2*T2-bound, so T2 is half of its right side.
    """
    height = I(HEIGHT)
    logh = height.ln()
    r = I('.112')*logh+I('.12567')*logh.ln()+I('3.77417')
    twice = ((height/(2*pi)).ln()+1)/(pi*height)
    twice = twice+(4*r+I('.112')+I('.12567')/logh)/(height*height)
    return twice/2


def all_inverse_square_sum(pi):
    """Upper bound for S = sum over ALL zeros with Im rho > 0 of 1/(Im rho)^2.

    By E3, N(u) = 0 for u < 14. For u >= 14, E2 gives
    N(u) <= u log(u)/(2 pi) - [u log(2 pi e)/(2 pi) - R(u)], and the bracket
    is nonnegative: it is positive at u = 14 and its derivative is at least
    log(2 pi e)/(2 pi) - (.112+.12567)/14 > 0 because log u >= 1 there.
    Hence S = 2 int_14^inf N(u) u^-3 du <= (log 14 + 1)/(14 pi).
    """
    start = I(14)
    slope = (2*pi).ln()+1
    slope = slope/(2*pi)                       # log(2 pi e)/(2 pi)
    r14 = I('.112')*start.ln()+I('.12567')*start.ln().ln()+I('3.77417')
    assert (start*slope-r14).lo > 0
    assert start.ln().lo >= 1
    assert (slope-(I('.112')+I('.12567'))/14).lo > 0
    return (start.ln()+1)/(14*pi)


def tilt_floor(tau_lo, width, claimed):
    """Assert 1-(1+tau^2/W^2)^(-1/2) >= claimed for every tau >= tau_lo.

    Equivalent to (1-claimed)^2 (1+tau_lo^2/W^2) >= 1, which avoids a
    square root. The left side increases with tau.
    """
    x = tau_lo*tau_lo/(I(width)*I(width))
    claimed = I(claimed) if not isinstance(claimed, I) else claimed
    assert 0 < claimed.hi < 1
    assert (((1-claimed)*(1-claimed))*(1+x)).lo >= 1
    return claimed


def main():
    pi = 16*atan(I(1)/5)-4*atan(I(1)/239)
    tau_lo, tau_hi = I(TAU1[0]), I(TAU1[1])
    t2 = tail_inverse_square_sum(pi)
    s_all = all_inverse_square_sum(pi)
    assert t2.hi < D('1.48e-12')
    assert s_all.hi < D('0.09')
    assert SPLIT <= WIDE <= HEIGHT

    # Lemma A (every derivative order n >= 0, 0 < w <= W):
    #   (-1)^n L^(n)(w) w^(n+1)/n!
    #       >= (2/tau_1^2) [1-(1+tau_1^2/W^2)^(-1/2)] - 4*T2 > 0.
    floor_split = tilt_floor(tau_lo, SPLIT, '0.18')
    margin_a = 2*floor_split/(tau_hi*tau_hi)-4*t2
    assert margin_a.lo > 0
    # For W = 10^5 use 1-(1+x)^(-1/2) >= 0.49 x at x = tau_1^2/W^2.
    x_wide = tau_lo*tau_lo/(I(WIDE)*I(WIDE))
    floor_wide = tilt_floor(tau_lo, WIDE, I('0.49')*x_wide)
    margin_a_wide = 2*floor_wide/(tau_hi*tau_hi)-4*t2
    assert margin_a_wide.lo > 0

    # Lemma C (first Hankel determinant, 0 < w <= W = 20):
    #   w^4 [L L'' - L'^2] >= 3/(W^2+tau_1^2)^2 - 96 S T2 - 48 T2^2 > 0.
    denominator = I(SPLIT)*I(SPLIT)+tau_hi*tau_hi
    main_c = 3/(denominator*denominator)
    loss_c = 96*s_all*t2+48*t2*t2
    margin_c = main_c-loss_c
    assert margin_c.lo > 0
    # How much larger could T2 be before either small-w lemma fails?
    slack_a = (2*floor_split/(tau_hi*tau_hi))/(4*t2)
    slack_c = main_c/loss_c
    assert slack_a.lo > 10**5 and slack_c.lo > 10**5

    # Lemma B (w >= W = 20, s = w+1/2 >= 20.5).
    # (i) Prime-sum bound: sum Lambda(n) log^j(n) n^-s <= 2^(3-s), j=0,1,2,
    #     and f(s) = (s-1)^3 2^(3-s) decreases for s >= 6, so for s >= 20
    #     f(s) <= f(20) = 19^3/2^17. The note needs f(s) <= 2 and the two
    #     weaker forms (s-1)^k 2^(3-s) <= 1, k = 1, 2, which follow.
    assert 19**3 < 2**17
    assert I(2).ln().lo*5 > 3                 # 6-1 > 3/log 2: f decreasing
    # (ii) with h = log(W/(2 pi))/2 <= kappa'(w):
    #     w^4 L''                >= 6h - 5/2             > 0,
    #     w^6 [L L'' - L'^2]     >= 2h^2 - h/2 - 1/4      > 0,
    #     the second because h > 1/2 (that is, W > 2 pi e) and the quadratic
    #     increases for h > 1/8.
    h = (I(SPLIT)/(2*pi)).ln()/2
    margin_b1 = 6*h-I(5)/2
    margin_b2 = 2*h*h-h/2-I(1)/4
    assert h.lo > D('0.5')
    assert margin_b1.lo > 0 and margin_b2.lo > 0

    print('T2 = sum_{Im rho > H} 1/(Im rho)^2  <=', t2.hi)
    print('S  = sum_{Im rho > 0} 1/(Im rho)^2  <=', s_all.hi)
    print('Lemma A margin, all orders, 0<w<=20   :', margin_a.lo)
    print('Lemma A margin, all orders, 0<w<=10^5 :', margin_a_wide.lo)
    print('Lemma C margin, Hankel, 0<w<=20       :', margin_c.lo)
    print('T2 could grow by these factors (A, C) :', slack_a.lo, slack_c.lo)
    print('Lemma B: h = log(20/(2 pi))/2 in', h)
    print('Lemma B margins at w=20 (L\'\', Hankel) :', margin_b1.lo, margin_b2.lo)
    print('PASS: constants for L\'\'>0 and L*L\'\'-(L\')^2>0 on w>0,'
          ' given E1-E3. Not a proof of RH.')


if __name__ == '__main__':
    main()
