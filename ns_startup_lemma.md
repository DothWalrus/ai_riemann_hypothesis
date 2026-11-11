# Unconditional startup lemma for the Nakamura–Suzuki screw function

This note gives an independently checked finite interval lemma for formula
(1.5) of Nakamura–Suzuki, *Statistics & Probability Letters* 201 (2023),
109889. It does not prove global nonpositivity or claim a new RH criterion.
The parent investigation reports that small interval positivity is already
discussed in Suzuki, *JLMS* (2023), DOI 10.1112/jlms.12785; this note's point
is to supply an elementary startup certificate usable by a finite checker.

**Lemma.** Unconditionally, `g_zeta(t)<0` for `0<t<=log(2)`.

Write

\[
C=-\tfrac12(\psi(1/4)-\log\pi)
 =\tfrac12\gamma+\tfrac\pi4+\tfrac32\log2+\tfrac12\log\pi.
\]

For `0<t<=log(2)` the prime contribution is zero, including the endpoint
where its sole possible summand has factor `t-log(2)=0`. Therefore `g=H`,
where expansion of the Lerch term gives

\[
H(t)=-4(e^{t/2}+e^{-t/2}-2)+Ct
 -\sum_{k=0}^\infty\frac{1-e^{-(2k+1/2)t}}{4(k+1/4)^2}.
\tag{1}
\]

The `k=0` term cancels the `e^{-t/2}` term, so equivalently

\[
H(t)=-4(e^{t/2}-1)+Ct
 -\sum_{k=1}^\infty\frac{1-e^{-(2k+1/2)t}}{4(k+1/4)^2}.
\tag{2}
\]

The series in (1) converges uniformly on compact subsets of `t>=0`,
and `H(0)=0`. Differentiation is justified locally uniformly for `t>0`.
It gives

\[
H''(t)=-e^{t/2}+\frac{e^{-t/2}}{e^{2t}-1}.
\tag{3}
\]

Its sign changes exactly once, from positive to negative. Indeed, with
`y=e^t>1` its sign is the opposite of `P(y)=y^3-y-1`, and `P` is strictly
increasing on `y>=1`. Let the sign change be `t_*`. The elementary
inequalities `P(e^{1/4})<0<P(e^{1/3})` imply

\[
1/4<t_*<1/3.
\tag{4}
\]

For the derivative, put `x=e^{-t/2}`. The identity

\[
\sum_{k\ge0}\frac{x^{4k+1}}{4k+1}
 =\int_0^x\frac{du}{1-u^4}
 =\tfrac12(\operatorname{atanh}x+\arctan x)
\]

yields the exact elementary expression

\[
H'(t)=-2(e^{t/2}-e^{-t/2})+C
       -\operatorname{atanh}(e^{-t/2})-\arctan(e^{-t/2}).
\tag{5}
\]

The standard-library interval computation in
`ns_startup_certificate.py` certifies the rational inequalities

\[
H(1/2)<-1/40,\qquad -1/32<H'(1/2)<0.
\tag{6}
\]

For the first bound it retains only `k=1,...,16` in (2), dropping a
strictly negative tail. The upper bound lies below
`-0.02524163494273708`. The interval for (5) lies between
`-0.028353306188511` and `-0.028353306188506`.

Concavity on `[t_*,infinity)` and its supporting tangent at `1/2` imply

\[
H(t)\le H(1/2)+H'(1/2)(t-1/2)
 <-\frac1{40}+\frac1{128}=-\frac{11}{640}<0
\]

for every `t>=t_*`: for `t<1/2`, use `t>=t_*>1/4`, and for `t>=1/2`
the tangent term is nonpositive. In particular `H(t_*)<0`.
On `[0,t_*]`, convexity puts `H` below the chord joining `(0,0)` to
`(t_*,H(t_*))`; hence `H(t)<0` for `0<t<=t_*` as well. This proves the
lemma.

## Certificate assumptions and reproducibility

Run `python3 ns_startup_certificate.py`. It uses 60 decimal digits with
directed rounding for arithmetic. Python Decimal's correctly rounded
`exp` and `ln` are enlarged by one ulp. Arctangent uses its alternating
series with the first omitted term as a two-sided error bound, while
`atanh` uses its positive series with a geometric tail bound. Pi follows
from Machin's identity. Euler's constant is bounded by the standard
Euler–Maclaurin estimate

\[
A_N-\frac1{120N^4}<\gamma<A_N,
\quad
A_N=H_N-\log N-\frac1{2N}+\frac1{12N^2},\quad N=1000.
\]

The script prints its intervals and asserts (4) and (6). It needs no
zero table, prime computation, nonstandard package, network, or RH input.

## First unresolved step

The proof actually shows the **prime-free smooth part** is negative
for every positive `t`. Starting at `log(2)`, the nonnegative prime sum
must be controlled. Its distributional second derivative adds the
positive atoms `Lambda(n)/sqrt(n)` at `t=log(n)`, so global concavity is
lost. Positivity of every individual atom also prevents extending the
startup tangent across a prime power. Bounds (3) and (5) support finite
gap certification, but they supply no global bound on the accumulated
prime contribution. The next test is a certified maximum on each gap
between successive prime powers, using concavity there and the exact
derivative jumps.
