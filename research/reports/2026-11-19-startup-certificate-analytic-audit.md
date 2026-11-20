# Independent audit of the combined explicit startup certificate

## Result and exact scope

[StartupCertificate.lean](../../formalization/RhCertificates/StartupCertificate.lean)
passes independent mathematical review and compiler replay. All five printed
declarations have only `propext`, `Classical.choice`, and `Quot.sound`.

The result is **kernel-checked and independently reviewed for the exact
series/formula defined in this project**. It proves the prime-free smooth
series is negative for all positive t, first for any C in `(2.68,2.691)`,
then for the exact defined gamma/pi/log constant. Adding the defined finite
weighted contribution preserves negativity for `0<t<=log(2)`.

No numerical or analytical sign hypothesis remains in the final instantiated
source-formula theorem. The added source bridges establish the digamma-quarter
constant, the convergent fixed-parameter Lerch defining series, actual von
Mangoldt weights, and the literal finite sum starting at n=1. The final theorem
proves sourceFormula(t)<0 for 0<t<=log(2), and sourceFormula(0)=0.
This is an explicit real-valued transcription of equation (1.5); no general
Lerch analytic-continuation theorem or global RH equivalence is asserted.
The statement does not control the prime contribution beyond the first event.

## Finite tangent estimates

The final finite-bound calculation was independently reviewed mathematically.
The exact Taylor estimates bound exp(1/4) in `[1.284,1.2841]` and its reciprocal
in `[10000/12841,250/321]`. These are kernel-derived bounds, not decimal inputs
asserted from Python.

At t=1/2, the exponential factor of term n is the `(4n+5)`th power of
x=exp(-1/4). Subtracting its upper power bound gives a lower bound for each
positive series summand. Sixteen terms exceed 0.23, so the upper C bound and
lower exponential bound yield H(1/2)<-0.02. Dropping the positive remaining
sum in this direction is valid.

For the derivative series, coefficient times rate is exactly `2/(4n+5)`.
Its first two positive terms exceed 0.13. For the remaining n>=2 terms,
the coefficient is at most 2/13 and the powers are dominated by a geometric
tail beginning at x^13 with ratio x^4. First two terms plus that tail are
less than 0.15. The summability and finite-plus-tail identities needed for the
inequalities are explicit.

Therefore C in `(2.68,2.691)` gives

    -0.04 < H'(1/2) < 0.

The directions agree: the lower bound uses C>2.68, exp(1/4)<=1.2841 and
series<0.15; the upper bound uses C<2.691, exp(1/4)>=1.284 and series>0.13.
In particular H(1/2)-H'(1/2)/4<-0.01. This is the exact margin needed by the
previously audited geometry theorem.

## Integration audit

The combined proof supplies continuity at zero, differentiability away from
zero and the actual second derivative using the explicit series theorems;
it does not reintroduce them as unproved assumptions. The curvature transition
and tangent/chord bounds are the already audited analytic geometry results.
The instantiated C enclosure is the separately kernel-checked constants
module, independently reviewed by a different agent.

The final finite-contribution transfer works for arbitrary weights. The
floor(exp(t)) cutoff and n>=2 force log(2)<=log(n)<=t, so t<=log(2) makes
each weighted factor zero, including n=2 at the endpoint. It assumes no
positivity or hidden arithmetic property of those weights.

## Final source-formula integration

The final sourceFormula proof rewrites the literal n=1 finite sum into the
normalized n=2 sum, uses the defining-series source identity for t>=0, and
applies the previously checked arbitrary-weight startup theorem to the actual
von Mangoldt weights. The strict-sign theorem supplies t>0, so the required
nonnegative source-identity domain is discharged rather than assumed.
At zero, the same identity and the zero prime contribution give the previously
proved smooth-series value zero. Both new declarations have been independently
read and replayed, with no extra hypothesis or numerical premise.

The n=1 reindexing lemma covers every natural cutoff, even empty intervals;
it removes only the known zero weight at 1. Independent review of the coefficient and Lerch modules authored by this
reviewer is assigned to another agent and recorded separately. This audit
addresses the final integration written by the parent.

## Replay and remaining global step

Independent replay, exit zero:

```sh
./formalization/lakew env lean RhCertificates/StartupCertificate.lean
```

Reviewed source hashes:

- StartupCertificate: `56f65dfa8a14c9250653202553b2f1d0b6539fc63335dd1b716474a61e080008`
- StartupFiniteBounds: `580e6eba08d15b4eb65bd967e8379850776c16a25aff67409e278cf0b4d7740f`

The successful combined build evidence is
[startup-certificate-build.txt](../../formalization/evidence/startup-certificate-build.txt).
No added mathematical axiom, unfinished proof, numerical enclosure hypothesis,
native-computation axiom, or Python PASS assumption appears in the final
instantiated theorem's dependency report.

The earlier audits' pending finite-tangent, coefficient and defining-series
representation steps are now discharged for the explicit real source formula.
The independent five-declaration replay is also preserved in
[startup-source-formula-analytic-replay.txt](../../formalization/evidence/startup-source-formula-analytic-replay.txt).
The global RH-strength accumulated-prime cancellation problem remains open.
No new zero-verification height or mathematical novelty is claimed.
