# Independent audit of the supported staircase countermodel

## Outcome and verification level

The abstract supported-staircase argument in
[PrimeSupport.lean](../../formalization/RhCertificates/PrimeSupport.lean) and
[its report](2026-11-19-prime-support-agent.md) passes this independent review.
The exact source was independently replayed successfully, and its 19 printed
axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

**Status: conditional kernel-checked and independently reviewed.** The event
sequence, a supported counting function, and that counting function's classical
PNT-shaped envelope are explicit hypotheses. They have not been instantiated
with actual prime powers and Chebyshev's function in this project. The model's
artificial weights are not the von Mangoldt weights. This is not an RH result
or a claim of mathematical novelty.

## Endpoint and construction audit

The strict-next-event definition is correct: `nextIndex(x)` is the first index
with `x<q_n`. For strictly increasing q, if `q_n<=x<q_(n+1)`, its value is n+1.
Consequently the constructed staircase is constant on the intervals `[q_n,q_(n+1))`, closed at the left
and open at the right, with value `q_(n+1)+q_0`.

Below the first event the constructed witness is zero. At the first event its
value is `q_1+q_0`, so the first jump has that size. At subsequent event q_n
its jump is `q_(n+1)-q_n>0`. Strict increase and unboundedness also imply only
finitely many events below a finite upper bound. The gap-coverage theorem
correctly covers the entire tail, so no unaccounted interval is omitted.

The right-continuity proof is substantive: at every x there is a b>x on which
the staircase is constant for x<=y<b. This includes an event itself and uses
the value after the jump. It matches the intended right-continuous convention.

The combined theorem records constant values on all event gaps, in addition
to normalization, monotonicity and right continuity. Full jump-measure language
is not formalized; the claim about support is understood through those exact
properties and the explicit staircase witness, not through an unstated measure
identity.

## Weighted-integral audit

Monotonicity of the constructed logarithmic staircase supplies interval
integrability. The exponential factors are continuous, so the weighted error
is integrable on each finite interval. Thus the combined theorem does not
assume integrability or the desired positive integral sign without proof.

With a=log(q_0)>0, the staircase is nonnegative before a and has surplus at
least exp(a)=q_0 after a. Applying the separately checked comparison lemma
gives

    weightedError(t) >= t+4-4 exp(a/2),  t>=a.

For t>=max(a,4exp(a/2)), the right-hand side is at least 4, proving strict
positivity. The inequality uses the correct sign of the kernel on the entire
integration interval. It is a result about the actual formal logarithmic
integral. Substitution to the original u-coordinate integral remains written
mathematics, as the agent report states.

## No-jump and PNT-envelope audit

The support hypothesis says `count(y)=count(x)` for x<=y<nextEvent(x).
The strict upper endpoint is essential and is used correctly. If the next
event equals x+h, the theorem permits that boundary event; it never assumes
constancy through an actual jump.

Put D(x)=x exp(-c sqrt(log x)) and h=4CD(x). The pointwise theorem explicitly
requires x>=1, C>0, c>=0, and 4Cexp(-c sqrt(log x))<=1. Thus x<=x+h<=2x.
Monotonicity of log, sqrt and the negative exponential gives D(x+h)<=2D(x).
The two endpoint counting bounds then imply

    count(x+h)-count(x) >= h-3CD(x) = CD(x)>0.

If x+h<nextEvent(x), this contradicts the no-jump premise. The resulting
next-event bound and the staircase's error bound have the correct factor 4
and retain the additive q_0 explicitly.

For c>0 the formal limit of exp(-c sqrt(log x)) is zero, so the smallness
condition eventually holds. The eventual theorem also enforces x>=X, ensuring
both counting bounds lie beyond the stated onset. Finally a squeeze argument
proves nextEvent(x)/x->1, and the additional q_0/x tends to zero. No sign
cancellation for the actual counting function is assumed or deduced.

## Replay and scope

Independent replay from the repository root, exit zero:

```sh
./formalization/lakew env lean RhCertificates/PrimeSupport.lean
```

Reviewed source SHA-256:
`4b1747a576747fc51cd7b997af76877d6654e55b532b1940b6b0d41effbdd85f`.
The owner's successful build evidence is
[prime-support-build.txt](../../formalization/evidence/prime-support-build.txt).
The pinned toolchain and manifest were retained. No new mathematical axiom,
unfinished proof, Python-result assumption or native-computation axiom appears
in the replayed dependency reports.

## Remaining step and next test

This closes the stated abstract integrability/support/asymptotic bridge that
was still written-only in the first artificial-staircase report. It does not
close the arithmetic bridge: the actual event enumeration, actual count's
support and its PNT estimate are still external premises. Even discharging
those premises would leave the constructed weights different from Lambda.

The next proof attempt about RH must therefore use an exact arithmetic
property which this artificial staircase lacks and derive a one-sided weighted
cancellation estimate from it. More support information or another two-sided
absolute error bound alone cannot repair the rejected deduction. Audit any
proposed divisor-identity argument separately; it is not covered by this report.
