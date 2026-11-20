# Independent audit of the positive-integer source sum

## Outcome

The frozen [StartupSourceSum.lean](../../formalization/RhCertificates/StartupSourceSum.lean)
source with SHA256
`4a2efec7d7098ad35385d464aaa32a41ed1cec2aebcc9056f018714fab9cc80b`
passed independent mathematical review and source replay. Both printed
declarations compile using only the standard three logical axioms.

**Verification level: kernel-checked finite-sum normalization.** This removes
the previously disclosed difference between the positive-integer sum beginning
at 1 and the normalized prime contribution beginning at 2. No novelty or RH
proof is claimed.

## Exact statement and endpoint checks

The coefficient is the actual
`StartupLerch.actualPrimeWeight(n)=vonMangoldt(n)/sqrt(n)`, with the already
proved identity `actualPrimeWeight(1)=0`. For every natural cutoff `N` and
every real `t`, the source proves

\[
\sum_{1\le n\le N}\frac{\Lambda(n)}{\sqrt n}(t-\log n)
=\sum_{2\le n\le N}\frac{\Lambda(n)}{\sqrt n}(t-\log n).
\]

The smaller finite set is explicitly a subset of the larger. Any removed index
has `n>=1` and cannot satisfy `n>=2`, so it is exactly 1; its entire summand
vanishes. The proof does not incorrectly require `N>=1` or `N>=2`. In particular,
both sums are empty at `N=0`, and the only extra term at `N=1` is zero.
The positive-integer convention excludes `n=0` throughout.

The definition `sourceFormula(t)` uses the smooth source expression plus the
positive-integer cutoff `N=floor(exp(t))`. The second theorem rewrites it exactly
as `StartupLerch.sourceFullExpression(t)`, with no changed constant, coefficient
normalization or cutoff.

This finite-sum equality is algebraically valid for all real t. The Lerch-series
identity giving the intended analytic source interpretation is separately
proved for `t>=0`; no convergent-series interpretation for negative t is silently
inferred from this elementary normalization.

## Independent replay and dependency audit

```sh
./formalization/lakew env lean RhCertificates/StartupSourceSum.lean
```

Exit status was zero with no warnings. Both declarations list exactly
`propext`, `Classical.choice`, and `Quot.sound`. There is no `sorryAx`, added
mathematical axiom or native-computation axiom. Evidence:
[startup-source-sum-independent-replay.txt](../../formalization/evidence/startup-source-sum-independent-replay.txt).
The environment pins Lean `leanprover/lean4:v4.35.0` and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

## Next integration test and remaining global gap

The next exact test is the final certificate that rewrites `sourceFormula`
through this equality and the already reviewed Lerch/digamma bridge, then
applies strict startup negativity on `0<t<=log(2)` and verifies the zero endpoint.

This normalization does not extend the sign certificate past the first prime
event and does not formalize the paper's RH equivalence. The unbounded
prime-contribution cancellation remains unresolved.
