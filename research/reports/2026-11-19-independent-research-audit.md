# Independent review of the curvature, series, and prime-obstruction results

## Plain-language outcome

The newly proved Lean statements inspected below are mathematically consistent
with their stated purposes. Independent compilation succeeded. The startup work
replaces some previously handwritten geometry and exponential estimates with
kernel-checked results. It still does not establish every hypothesis for the
actual auxiliary function. The prime-obstruction work proves that certain
coarse estimates alone cannot justify the proposed global sign argument; it
is not a result about actual prime weights or an RH counterexample.

**Review status:** complete for the exact statements and mathematical proofs
listed below and for the written staircase argument. The complete analytic
bridge to the actual screw function, and a full Lean construction of the
actual next-prime-power staircase, remain incomplete. No novelty is claimed.

## Curvature: independently replayed and reviewed

[Curvature.lean](../../formalization/RhCertificates/Curvature.lean) was independently
recompiled successfully. All eight listed public declarations report only
`propext`, `Classical.choice`, and `Quot.sound`.

The normalization is correct. If `r=exp(t/2)` and `y=exp(t)`, then `r^2=y`,
and the proposed curvature is

    -r + (1/r)/(y^2-1) = -(y^3-y-1)/(r*(y^2-1)).

For `t>0` the denominator is positive, so the curvature has the cubic's
opposite sign. This is the same H'' expression appearing in the startup note,
with no missing factor or exponent.

The cubic is strictly increasing for `y>=1`. The exact Taylor bound
`exp(1/4)<13/10` puts its value below `P(13/10)=-103/1000`, and
`exp(1/3)>=4/3` puts its value above `P(4/3)=1/27`. The Lean proof uses a
Mathlib exponential remainder theorem rather than Python decimal output.
Continuity and the intermediate value theorem produce a transition strictly
between `1/4` and `1/3`; monotonicity gives the two curvature signs on the
correct sides. The endpoint is included correctly in both non-strict signs.

**Certified scope:** an exact result about the displayed exponential expression.
It does not by itself prove that any specified series-defined H has that
second derivative.

## Smooth series: independently replayed and reviewed

[SmoothSeries.lean](../../formalization/RhCertificates/SmoothSeries.lean) was
independently recompiled successfully at its 15-declaration checkpoint, all
with the standard three logical axioms.

The index shift is correct: natural index `n=0` denotes written index `k=1`.
The coefficient `4/(4n+5)^2` equals `1/(4(n+1+1/4)^2)`, and the rate
`2n+5/2` equals the written exponent coefficient. Their product satisfies
`coefficient * rate^2 = 1`, as required for the second derivative cancellation.

For nonnegative t, each term is nonnegative and bounded in norm by
`1/(n+1)^2`. The summable dominator justifies the series continuity on the
closed half-line, including zero, and the value there is zero. The individual
term derivative and the derivative of that derivative have the correct signs.
The exponential tail is exactly a geometric series, with sum

    exp(-t/2)/(exp(2t)-1),  t>0.

The source's domain restrictions avoid a hidden differentiability assumption
at zero. Its arbitrary linear coefficient C is explicit; no claim that it has
the special numerical value is introduced.

**Certified scope at this checkpoint:** series convergence/continuity and
individual-term derivatives plus the geometric tail identity. These facts do
not alone justify interchanging a derivative and the infinite sum. Uniform
local derivative bounds and a suitable termwise differentiation theorem still
need to be applied. Later additions to the file need separate review.

## Startup geometry: independently replayed and reviewed

[StartupGeometry.lean](../../formalization/RhCertificates/StartupGeometry.lean)
was independently recompiled after its derivative-sign and curvature-formula
wrappers were added. The wrappers use continuity on the nonnegative half-line
and differentiability of f and its derivative only on the positive half-line.
They obtain closed-interval convexity and tail concavity from the interior
curvature signs. Thus they do not silently require a finite derivative at zero.

The resulting strict-negativity theorem is a **conditional kernel-checked**
implication. It assumes the analytic differentiability/curvature facts for f,
its zero value, and the tangent value/slope bounds. It does not certify those
facts for the actual H or g. The generic chord and tangent statements are
kernel-checked mathematical results in their own right.

## Smooth prime-obstruction model: independently replayed and reviewed

[PrimeObstruction.lean](../../formalization/RhCertificates/PrimeObstruction.lean)
was independently recompiled successfully, with 11 listed public declarations
using only the standard three logical axioms. Its definitions are artificial
and use logarithmic coordinates; they are not definitions of actual Chebyshev
psi or the zeta function.

For nonnegative t, the model

    psi_model(t) = exp(t)+exp(3t/4)-2

is normalized at zero, nonnegative and monotone. The error has absolute value
at most `exp(3t/4)`, because that exponential is at least one. After division
by `exp(t)`, the relative error is at most `exp(-t/4)`. The PNT-shaped envelope
for t=v^2 uses the exact sufficient condition `v>=4c`, with `c>=0`.

The fundamental-theorem-of-calculus proof is an actual integral proof. The
primitive's derivative is the defined integrand, and its endpoint values give

    weightedError(t) = 12 exp(t/4)-12-4t.

Using `exp(t/8)>=1+t/8` yields the lower bound `t(3t-16)/16`, strictly positive
for `t>=6`. This independently confirms the constants and positivity threshold.

**Scope boundary:** the integral substitution between x-coordinates and
logarithmic coordinates is written mathematics in the report, not an additional
Lean theorem. Likewise the asymptotic limit follows from the relative-error
bound but is not separately compiled in this file. No actual Lambda-weight
claim follows from the model.

## Prime-power staircase: written argument independently reviewed

The construction in [the prime-agent report](2026-11-19-global-prime-agent.md)
uses the least prime power strictly greater than x. Strictness matters:
`q_+(x)` is constant on `[q_i,q_(i+1))` and equals `q_(i+1)` at the left
endpoint. Therefore the defined staircase is right-continuous, with first jump
5 at 2 and positive subsequent jumps `q_(i+1)-q_i`. Its normalization and
claimed support are correct. The weights are changed and generally are not
Lambda weights; the report states this essential limitation.

The gap estimate from the stated actual-PNT premise also checks. Write
`f(x)=exp(-c sqrt(log x))` and `h=4Cxf(x)`. Eventually h<=x. If there were no
prime power in `(x,x+h]`, the actual Chebyshev function would be constant there.
Its two error bounds, monotonicity of f, and x+h<=2x would give

    psi(x+h)-psi(x) >= 4Cxf(x)-2Cxf(x)-Cxf(x) = Cxf(x)>0,

contradicting constancy. Thus the next prime power is within h. The artificial
staircase error is at most h+2, and the additive 2 is absorbed asymptotically
because xf(x) tends to infinity. The actual-PNT estimate is an explicit
external premise; it is neither reproved nor kernel-certified here.

The weighted-integral comparison is also correct. Before u=2 the error is
`-u`; afterward it is at least 2. Integrating these lower errors gives
`t+4-4 sqrt(2)` for x=exp(t), t>=log(2). The conditional Lean comparison
`weightedError_lower_of_surplus` matches this calculation with `a=log(2)`.
The staircase's construction, integrability and instantiation remain written
obligations, not claims certified by that conditional theorem alone.

## Replay and version scope

Independent commands, each exit zero, from the repository root:

```sh
./formalization/lakew env lean RhCertificates/Curvature.lean
./formalization/lakew env lean RhCertificates/SmoothSeries.lean
./formalization/lakew env lean RhCertificates/PrimeObstruction.lean
./formalization/lakew env lean RhCertificates/StartupGeometry.lean
```

The environment is pinned by `formalization/lean-toolchain` and
`formalization/lake-manifest.json`. No new mathematical axiom, unfinished proof,
or native-computation axiom appeared in the printed dependency reports.

The three source hashes at the reviewed checkpoint were:

- Curvature: `dc33af78b9ef65f0892d55bbe7d6b496c2d72b9db76389ba698bc0c55f45fb2a`
- SmoothSeries: `03bbd38bbc26879b87d054948a12993fa4660adff6c0c03c052d829f19c1f1ff`
- PrimeObstruction: `32127cbdab7cd152a9c5a5ab3e5fcd8f00a369ad0ce878938a92b0868dc70763`

## Exact remaining step and next test

For the startup route, independently review the next termwise differentiation
bridge before identifying the series-defined function's second derivative with
the proved curvature expression. Then prove the special intercept and slope
bounds in the kernel. For the global prime route, the unresolved step is a
one-sided cancellation estimate using the exact actual Lambda weights, not
just normalization, monotonicity, jump support or a two-sided error envelope.

The next test for the prime construction is the abstract event-sequence model
being developed separately. Its conclusions must remain conditional on explicit
event/support/integrability premises until those are instantiated; even a fully
formal artificial staircase is not a result about the Riemann hypothesis.
