# Prime contribution on the startup interval

## Outcome and verification level

**Kernel-checked:** the displayed finite prime contribution vanishes whenever
`t<=log(2)`, including the first prime-event endpoint. The coefficients can be
arbitrary real weights. A separate implication transfers a proved smooth-part
sign to the displayed full formula on `0<t<=log(2)`.

This is elementary finite-sum bookkeeping. No novelty or RH result is claimed.
The formula is defined explicitly in Lean; its identity with the published
screw function is not asserted automatically.

## Exact formula and argument

In [PrimeStartup.lean](../../formalization/RhCertificates/PrimeStartup.lean),
`primeContribution weight t` is

\[
\sum_{2\le n\le\lfloor e^t\rfloor}
   \operatorname{weight}(n)\,(t-\log n).
\]

For every permitted index, `n>=2` gives `log(n)>=log(2)`. The upper cutoff
`n<=floor(exp(t))` gives `log(n)<=t`. If `t<=log(2)`, the two bounds force
`log(n)=t`, so every factor `t-log(n)` is exactly zero. This proves
`primeContribution_zero` for all real `t<=log(2)`. In particular, the possible
`n=2` term at the endpoint is zero; the proof does not incorrectly exclude it.

The stronger helper `weighted_sum_zero_of_log_cutoff` works for any finite set
whose indices obey `n>=2` and `log(n)<=t`. It does not need any positivity or
arithmetic property of the weight.

The definition `fullExpression C weight t` is the defined smooth series plus
this contribution. `fullExpression_eq_smoothPart` identifies the two expressions
through the first event. `fullExpression_negative_on_startup` then states:
if the defined smooth series is negative for every positive argument, the
defined full expression is negative on `0<t<=log(2)`.

## Replay and dependency audit

```sh
./formalization/lakew env lean RhCertificates/PrimeStartup.lean
```

The final source compiles with exit status zero and no warnings. All four
printed declarations have exactly `propext`, `Classical.choice`, and
`Quot.sound`; no added mathematical axiom or unfinished proof occurs. See
[prime-startup-build.txt](../../formalization/evidence/prime-startup-build.txt).
The project pins Lean `leanprover/lean4:v4.35.0` and Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`. An independent replay/review of
this small module remains to be recorded.

## Remaining step and next test

The weight may later be instantiated as `Lambda(n)/sqrt(n)`. A full formal
identification with the published screw function requires representing its
other terms and the constant consistently, rather than treating this arbitrary
weight theorem as that identification. The immediate next test is to combine
the completed smooth-series sign certificate with this transfer theorem for
the same exact constant and formula.

Past `log(2)`, a nonzero prime contribution appears. This vanishing argument
offers no control over its accumulated contribution on an unbounded domain.
