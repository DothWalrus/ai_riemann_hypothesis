# Coarse exact bounds for the startup linear constant

## Plain-language result

Lean now proves a sufficiently tight interval for the real constant appearing
in the written startup series. This removes one set of formerly external
numerical inputs without assuming a decimal answer or a Python result. It is
an elementary certificate for a named constant, not a proof of RH.

**Status: kernel-checked.** Five declarations compile in the pinned environment,
with only `propext`, `Classical.choice`, and `Quot.sound` in their axiom reports.
No mathematical axioms, unfinished proofs, native-computation certificates, or
numerical hypotheses were added.

## Exact statement

[StartupConstants.lean](../../formalization/RhCertificates/StartupConstants.lean)
defines

\[
C=\frac{\gamma+\pi/2+3\log 2+\log\pi}{2},
\]

where gamma is Mathlib's real Euler--Mascheroni constant. The theorem
`RhCertificates.startupConstant_bounds` proves

\[
\frac{67}{25}<C<\frac{2691}{1000},
\]

or `2.68<C<2.691`. These are exact rational bounds on real expressions.

## Derivation and numerical trust boundary

The Mathlib increasing and decreasing harmonic-log sequences give

    harmonic(63)-log(64) < gamma < harmonic(64)-log(64).

Exact rational finite sums establish

    harmonic(63)>4.728,     harmonic(64)<4.744.

The identity `log(64)=6log(2)` and Mathlib's already proved rational bounds
`0.6931471803<log(2)<0.6931471808` yield

    0.569<gamma<0.586.

For log(pi), the proof uses the positive series for
`log((1+x)/(1-x))/2`. Eight terms at the rational values `107/207` and
`1071/2071` give lower and upper bounds for `log(3.14)` and `log(3.142)`.
The upper bound includes Mathlib's explicit geometric remainder. Monotonicity
of log and existing proved pi bounds then give

    1.144<log(pi)<1.145.

Combining these inequalities with `3.14<pi<3.1416` and the proved log(2)
bounds yields the main enclosure by rational linear arithmetic. In particular,
no correctly-rounded Decimal primitive is trusted by this proof; the
transcendental inequalities come from formal Mathlib theorems.

The pinned primary sources inspected locally were
[Mathlib's Euler--Mascheroni construction](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/NumberTheory/Harmonic/EulerMascheroni.lean),
[pi bounds](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Real/Pi/Bounds.lean), and
[logarithm series bounds](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean).

## Replay and evidence

From the repository root:

```sh
./formalization/lakew env lean RhCertificates/StartupConstants.lean
```

The source compiled successfully. The replay output and exact environment
pins are preserved in
[startup-constants-build.txt](../../formalization/evidence/startup-constants-build.txt).
Initial development failures concerned casts and rational normalization;
those were corrected. Only the clean final compilation is counted as evidence.

The public checked declarations are `startupConstant_eq`, `log_sixtyfour`, `gamma_coarse_bounds`,
`log_pi_coarse_bounds`, and `startupConstant_bounds`.

## Scope, remaining step and next test

This certifies the displayed gamma/pi/log expression. Identifying it with the
coefficient written using the digamma value at 1/4 requires the corresponding
special-function identity; that identity is written in the project note and
is not proved in this new file. The full original screw-function definition
and its equality with the explicit smooth series also remain separate links.

The next test is to derive the startup series' intercept and slope bounds
from this exact enclosure and kernel-checked exponential/series estimates,
then apply the already formalized geometric implication. Parent work owns
that finite bound calculation, so this file deliberately supplies only the
constant enclosure and does not duplicate it.

Independent review of this new constant proof is still requested. The earlier
independent audits of other modules do not automatically cover it.
