# Independent geometry-agent audit of the integrated startup certificate

## Outcome

The integrated [StartupCertificate.lean](../../formalization/RhCertificates/StartupCertificate.lean)
passed independent mathematical review and an independent source replay.
All five final declarations compile using only `propext`, `Classical.choice`,
and `Quot.sound`.

**Verification level: kernel-checked for the exact series and nonnegative-argument
source-formula transcription.** The integrated result has no assumed decimal
bound, external Python result, unproved curvature formula or termwise
differentiation premise. No novelty or RH proof is claimed.

## Exact meaning

For the exact constant

\[
C=(\gamma+\pi/2+3\log2+\log\pi)/2,
\]

the theorem `smoothPart_startupConstant_negative` proves that the explicitly
defined prime-free series `SmoothSeries.smoothPart C t` is strictly negative
for every real `t>0`.

The theorem `fullExpression_startupConstant_negative` proves strict negativity
of the defined smooth series plus its finite prime contribution for
`0<t<=log(2)`. The coefficient function in that finite contribution may be
arbitrary, because every term vanishes on this interval, including the endpoint.

The final two declarations additionally prove strict negativity for the exact
positive-integer source-formula transcription on `0<t<=log(2)` and its value
zero at `t=0`. The digamma coefficient and convergent fixed Lerch defining series
are now linked by proved identities, rather than by an assumed equality.
Its conclusion for every positive argument still concerns only the prime-free
smooth part; the full source formula has the stated finite startup interval.

## Integration checks

1. The exact constant enclosure supplies both hypotheses needed by the
   finite-bound module; no constant interval remains assumed in the final
   fixed-constant theorem.
2. The exact finite estimates give `H(1/2)<-1/50` and
   `-1/25<D(1/2)<0`. The derivative-series theorem proves that `D(1/2)` is
   the actual derivative of the defined `H`.
3. Those estimates give the flexible margin
   `H(1/2)-D(1/2)/4<-1/100<0`, and the nonpositive-slope premise is supplied
   separately. Thus the margin geometry is applied with the correct sign.
4. Continuity on `[0,infinity)`, `H(0)=0`, differentiability of `H` and `deriv H`
   on `(0,infinity)`, and the exact second-derivative formula are all proved
   in the imported series modules. The curvature transition and closed-endpoint
   chord are therefore consequences of proved inputs.
5. The finite-prime contribution vanishing theorem transfers the result only
   on `t<=log(2)`. There is no extension of that vanishing premise across later
   prime events.
6. The final source theorem normalizes the positive-integer cutoff beginning
   at 1, uses the proved vanishing `n=1` weight, then rewrites through the
   convergent Lerch-series and digamma-coefficient identities. The Lerch bridge
   is invoked only at nonnegative arguments, where its series converges.
7. The zero-endpoint theorem uses the separate exact `H(0)=0` result after
   these rewrites. It does not apply the strict positive-argument sign theorem
   at a point excluded by that theorem's hypotheses.

I also independently reviewed and replayed the supporting
[constant bounds](2026-11-19-startup-constants-independent-audit.md) and
[finite value/slope bounds](2026-11-19-startup-finite-bounds-independent-audit.md).
The separate auditor reviewed and replayed the geometry and analytic derivative
bridge in [its report](2026-11-19-smooth-derivatives-independent-audit.md).

## Independent replay and dependencies

```sh
./formalization/lakew env lean RhCertificates/StartupCertificate.lean
```

The final source SHA256 is
`56f65dfa8a14c9250653202553b2f1d0b6539fc63335dd1b716474a61e080008`.
The command exited with status zero and no warnings. All five `#print axioms`
outputs contain exactly the standard three logical axioms, with no `sorryAx`,
new mathematical axiom or native-computation axiom. Evidence is in
[startup-certificate-geometry-replay.txt](../../formalization/evidence/startup-certificate-geometry-replay.txt).
Lean is pinned to `leanprover/lean4:v4.35.0` and Mathlib to
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

## Remaining mathematical gap and next test

The digamma special value, fixed-parameter convergent Lerch-series reduction,
and positive-integer finite-sum normalization are now separately proved and
integrated. Their independent audits are the
[digamma review](2026-11-19-startup-digamma-independent-audit.md),
[Lerch review](2026-11-19-startup-lerch-independent-audit.md), and
[source-sum review](2026-11-19-startup-source-sum-independent-audit.md).
This is a formal transcription using the defining series in its convergent
domain, not a general Lerch analytic-continuation development or a formalization
of the paper's RH-equivalence theorem.

For the RH investigation itself, later prime events contribute nonzero terms.
Their accumulated cancellation for an unbounded argument remains uncontrolled.
This startup certificate does not imply the required global sign for the full
screw function and does not settle RH.
