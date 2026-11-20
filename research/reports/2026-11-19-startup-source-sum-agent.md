# Literal positive-integer source-sum normalization

## Result and status

**Kernel-checked:** the literal finite sum from n=1 through floor(exp(t))
equals the previously normalized sum starting at n=2 for the actual weights
`Lambda(n)/sqrt(n)`. The proof removes only the zero n=1 term and works even
when the cutoff is below 1. It has no prime-counting, RH or numerical premise.

The two declarations in
[StartupSourceSum.lean](../../formalization/RhCertificates/StartupSourceSum.lean)
compile without warnings and use only `propext`, `Classical.choice`, and
`Quot.sound`. Independent review and replay are requested separately.
No novelty or RH proof is claimed.

## Exact formula and argument

The new definition is the direct positive-integer-sum transcription

\[
\operatorname{sourceFormula}(t)=H_{\rm src}(t)+
 \sum_{1\le n\le\lfloor e^t\rfloor}
 \frac{\Lambda(n)}{\sqrt n}\,(t-\log n),
\]

where H_src is the explicit digamma/Lerch-defining-series expression in
[StartupLerch.lean](../../formalization/RhCertificates/StartupLerch.lean).
That module also defines the actual weights and proves the weight at 1 is zero.

For every natural cutoff N, the interval `{2,...,N}` is a subset of `{1,...,N}`.
An index in the larger interval but not the smaller interval must be exactly 1.
Its summand vanishes because its actual weight is zero. The finite `sum_subset`
theorem therefore proves

    sum(n=1..N) actualWeight(n)*(t-log(n))
      =sum(n=2..N) actualWeight(n)*(t-log(n)).

This is the exact helper `positive_sum_eq_normalized_sum`; its quantification
includes every N and every real t. Empty intervals require no separate
exception or inaccurate assumption that floor(exp(t)) is at least 1.

The theorem `sourceFormula_eq_sourceFullExpression` applies the helper to the
actual cutoff and proves equality with `StartupLerch.sourceFullExpression`.
The intended source interpretation uses t>=0, as does the original paper's
formula; the finite algebraic identity itself is valid for every real t.
No claim about the source's even extension to negative t is made.

## Replay and remaining integration

From the repository root:

```sh
./formalization/lakew build RhCertificates.StartupLerch
./formalization/lakew env lean RhCertificates/StartupSourceSum.lean
```

The final replay exits zero. See
[startup-source-sum-build.txt](../../formalization/evidence/startup-source-sum-build.txt)
for the command, pins and axiom report. The module does not import the final
StartupCertificate module, so integrating its equality there is acyclic.

The next test is independent replay and substitution of this equality, followed
by the checked source-series identity and startup sign certificate. This will
make the final theorem name an explicit formula whose finite sum starts at 1;
no finite-index reindexing step remains merely handwritten.

A general RH equivalence, behavior beyond the first prime event, or global
prime cancellation is not supplied by this bookkeeping result.
