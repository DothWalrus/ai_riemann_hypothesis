# A checked startup certificate for the explicitly defined formula

The project now has a Lean proof of strict negativity on the initial interval
for a transcription of Nakamura--Suzuki's defining formula (1.5). The proof
includes the digamma coefficient, convergent Lerch defining series, actual
von Mangoldt weights, infinite-series analysis and numerical bounds. It does
not assume a Python result or merely check the last arithmetic comparison.

**This is a finite formalization result, not a proof of RH, a new zero check,
or a claim of a novel mathematical theorem.** The paper's global RH criterion
and zero expansion are not proved by this certificate.

## Exact result

Define the real constant

`C=(EulerGamma + pi/2 + 3*log(2) + log(pi))/2`

and, for `t>=0`, the convergent real series

`H(t)=-4*(exp(t/2)-1)+C*t-sum_{k>=1}(1-exp(-(2k+1/2)*t))/(4*(k+1/4)^2)`.

Lean proves `H(t)<0` for **every `t>0`**. This is the smooth part; it does not
include the prime sum that prevents the same argument from proving RH.

For any weight function `w : Nat -> Real`, define the finite formula

`G_w(t)=H(t)+sum_{2<=n<=floor(exp(t))} w(n)*(t-log(n))`.

Lean proves `G_w(t)<0` whenever `0<t<=log(2)`. On that interval each permitted
term vanishes, including the possible `n=2` term at the endpoint. The theorem
does not assume positivity, arithmetic structure, or any property of `w`.

The exact final declarations in
[StartupCertificate.lean](../../formalization/RhCertificates/StartupCertificate.lean)
are `smoothPart_startupConstant_negative` and
`fullExpression_startupConstant_negative`. The additional theorem
`sourceFormula_negative_on_startup` proves the strict sign of the source
transcription on `0<t<=log(2)`, with `sourceFormula_zero` proving its value
zero at the endpoint `t=0`.

**Verification level: kernel-checked for these explicitly defined objects.**
There are no remaining analytic, numerical, or RH hypotheses in these two
instances. The parameter `w` is universally quantified.

## What the certificate checks

1. The infinite-sum component has a summable uniform inverse-square majorant
   on the nonnegative half-line. This justifies continuity at zero and the
   value zero there. The full smooth function, which contains an exponential
   term, is not asserted to be bounded on that half-line.
2. Locally away from zero, geometric majorants justify differentiating the
   infinite series twice. The exact second derivative is
   `-exp(t/2)+exp(-t/2)/(exp(2*t)-1)`.
3. Its sign changes from nonnegative to nonpositive at a point strictly between
   `1/4` and `1/3`. The exponential estimates, cubic monotonicity and intermediate
   value argument are proved in Lean.
4. Harmonic-number bounds on Euler's constant, rational pi bounds and analytic
   logarithm bounds give `2.68<C<2.691`.
5. Exact Taylor bounds and rational comparisons give `H(1/2)<-1/50` and
   `-1/25<H'(1/2)<0`. The value bound drops a nonnegative infinite tail after
   16 terms. The derivative bounds include a proved geometric tail estimate;
   that tail is not simply discarded in the wrong direction.
6. Concavity gives the supporting tangent on the tail, while convexity and
   continuity at zero give the initial chord. The tangent margin is strictly
   negative. No finite derivative at zero is assumed.
7. The actual floor/log cutoff proves the finite extra contribution is zero
   throughout the startup interval.

## Source-expression bridge and scope

The source is Nakamura and Suzuki (2023),
[equation (1.5)](https://doi.org/10.1016/j.spl.2023.109889). Its digamma constant
is identified exactly with `C` in
[StartupDigamma.lean](../../formalization/RhCertificates/StartupDigamma.lean).
[StartupLerch.lean](../../formalization/RhCertificates/StartupLerch.lean)
defines `Phi(q)=sum_{n>=0} q^n/(n+1/4)^2`, proves convergence for `0<=q<=1`,
and proves the first-term cancellation and full smooth-expression identity.
No meromorphic continuation is substituted for a divergent ordinary sum.

The actual weights `Lambda(n)/sqrt(n)` are used in the source expression.
[StartupSourceSum.lean](../../formalization/RhCertificates/StartupSourceSum.lean)
proves that its positive-integer finite sum starting at 1 equals the normalized
sum starting at 2; `Lambda(1)=0` is proved and empty cutoffs are handled. The
source transcription was compared directly with the supplied paper's page 2
and independently reviewed, including coefficients, signs, exponents and the
definition printed there for the Lerch series.

This result concerns an initial
interval of the full formula. The positive prime contribution for unbounded
arguments remains uncontrolled. No finite certificate proves the global sign.

## Replay, evidence, and independent review

Use the committed Lean `v4.35.0` toolchain and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`:

```sh
./formalization/lakew build
./formalization/lakew env lean RhCertificates/StartupCertificate.lean
python3 scripts/verify_lean_certificates.py
```

The last command builds the registered project modules, independently
recompiles their sources, saves fresh `formalization/evidence/replay-*.txt`
logs, and checks every explicit `#print axioms` declaration. It does not
replace review of theorem statements or certify unrelated repository prose.

The direct final report is
[startup-certificate-build.txt](../../formalization/evidence/startup-certificate-build.txt),
now including the source-formula and zero-endpoint theorems.
The numerical bridge is in
[StartupFiniteBounds.lean](../../formalization/RhCertificates/StartupFiniteBounds.lean),
with [its replay](../../formalization/evidence/startup-finite-bounds-build.txt).
All printed axiom dependencies are restricted to `propext`, `Classical.choice`
and `Quot.sound`. No `sorry`/`admit`, custom mathematical axiom,
`native_decide` certificate, or Python interval premise is used.

Independent agents reviewed and replayed the component proofs and the final
combination. See the separate
[geometry-agent audit](2026-11-19-startup-certificate-geometry-audit.md) and
[analytic-agent audit](2026-11-19-startup-certificate-analytic-audit.md),
the [finite-bound audit](2026-11-19-startup-finite-bounds-independent-audit.md),
and the [series-differentiation audit](2026-11-19-smooth-derivatives-independent-audit.md).
Kernel checking and independent interpretation review are separate checks;
agent agreement alone would not be a certificate.

## Exact next step

The next global proof attempt must address cancellation in the actual prime weights for
unbounded arguments. The separate arithmetic-obstruction reports rule out
specific overly coarse or positive-combination deductions, not RH itself.
