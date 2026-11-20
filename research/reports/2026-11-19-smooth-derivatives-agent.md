# Differentiation of the smooth-part series

## Outcome in plain language

The infinite series defining the prime-free smooth part can now be
differentiated twice in Lean at every positive argument. The proof controls
the whole infinite tail locally, so this step no longer relies on a Python
calculation or on informal termwise differentiation. It includes the exact
second-derivative formula used in the startup argument.

**Verification level: kernel-checked for the explicitly defined real series.**
Application to the published screw function and its specific linear constant
requires the remaining identification and numerical steps described below.
This is a formalization of an elementary analytic argument, with no novelty
claim and no proof of RH.

## Exact function and checked results

The definitions are in [SmoothSeries.lean](../../formalization/RhCertificates/SmoothSeries.lean).
For natural `n`, write

\[
a_n=\frac4{(4(n+1)+1)^2},\qquad r_n=2(n+1)+\frac12,
\]

\[
H_C(t)=-4(e^{t/2}-1)+Ct-\sum_{n\ge0}a_n(1-e^{-r_nt}).
\]

This index starts with `k=n+1` in the written startup note. The linear
coefficient `C` is an arbitrary real number here.

The new source [SmoothDerivatives.lean](../../formalization/RhCertificates/SmoothDerivatives.lean)
proves the following for every real `C` and every `t>0`:

\[
H_C'(t)=-2e^{t/2}+C-\sum_{n\ge0}a_nr_ne^{-r_nt},
\]

\[
H_C''(t)=-e^{t/2}+\frac{e^{-t/2}}{e^{2t}-1}.
\]

The primary declarations, in namespace `RhCertificates.SmoothSeries`, are
`smoothPart_hasDerivAt`, `smoothPart_deriv`, `smoothPart_deriv_hasDerivAt`,
and `smoothPart_second_deriv`. The theorems `differentiableOn_smoothPart` and
`differentiableOn_smoothPart_deriv` give differentiability of the function and
its derivative on `(0,infinity)`.

The separate series module already proves continuity on `[0,infinity)` and
`H_C(0)=0`. No derivative at zero is asserted or needed.

## Infinite-tail control and derivative interchange

The exact identity `a_n*r_n^2=1`, together with `r_n>=1`, yields
`0<=a_n*r_n<=1`. For every `s>=b>0`, both the first-derivative term and the
absolute value of its derivative are bounded by `exp(-r_n*b)`.
This majorant is summable by the separately checked geometric-series formula.

At a given `t>0`, use the open, preconnected half-line `(t/2,infinity)`.
The original series is summable at the basepoint `t`, and its derivative
series has the summable uniform majorant above. Mathlib's
`hasDerivAt_tsum_of_isPreconnected` therefore justifies the first interchange.
The first derivative series also converges at `t`, with the same majorant,
so a second application justifies its derivative interchange. The exact
geometric sum supplies the displayed formula for `H_C''`.

Finally, the first derivative is identified with `deriv (smoothPart C)` on a
neighborhood of each positive point. The second derivative is transferred by
eventual equality, rather than identifying functions only at a single point.

## Replay and axiom report

From the repository root:

```sh
./formalization/lakew env lean RhCertificates/SmoothDerivatives.lean
```

The latest direct source compilation exited with status zero. All fifteen
printed declarations have exactly `propext`, `Classical.choice`, and
`Quot.sound` in their axiom reports. See
[smooth-derivatives-build.txt](../../formalization/evidence/smooth-derivatives-build.txt).
There are no unfinished proofs, added mathematical axioms, native-computation
oracles, or external numerical assumptions. Lean is pinned to
`leanprover/lean4:v4.35.0` and Mathlib to
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

An initial draft failed only where imported definition bodies were hidden by
Lean's module interface. Public defining equations and explicit body exposure
were added; the full file subsequently compiled. That failed draft is not used
as evidence.

## Independent review

The independent startup auditor mathematically checked the summable-majorant
argument, both interchange applications, endpoint exclusion, derivative scaling,
and the eventual-equality step, and found no hidden analytic assumption. An
independent compiler replay of this final source also passed; see
[the independent audit](2026-11-19-smooth-derivatives-independent-audit.md).

## Exact remaining obligation and next test

The series differentiation gap is closed for `H_C`. The next test is to combine
this module with the compiled curvature transition and startup geometry and
prove explicit bounds at `t=1/2` for the intended linear constant. The flexible
geometry API needs only `H_C'(1/2)<=0` and
`H_C(1/2)-H_C'(1/2)/4<0`.

The specific value of `C`, its exact numerical enclosure, the identity with the
published prime-free part, and the vanishing prime contribution on the startup
interval must still be represented and checked before calling the full startup
sign result Lean-certified. None of these finite startup steps establishes
global nonpositivity of the full screw function beyond the first prime event.
