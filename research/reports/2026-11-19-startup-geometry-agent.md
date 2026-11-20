# Startup geometry: conditional Lean certificate

## Outcome in plain language

Lean now checks the geometric step of the startup argument: a function that
first bends upward and then bends downward stays below zero if its value and
slope at one specified point satisfy the explicit bounds. The tangent and
chord bounds are derived from convexity and concavity, rather than assumed.
This does not yet prove that the actual Nakamura--Suzuki smooth part satisfies
the analytic or numerical hypotheses, and does not prove RH.

**Verification level: conditional kernel-checked.** The implications for an
arbitrary real function compile with pinned Lean/Mathlib. Their application to
the actual smooth part is still conditional. No novelty is claimed.

## Exact statements and hypotheses

Source: [StartupGeometry.lean](../../formalization/RhCertificates/StartupGeometry.lean).

1. `RhCertificates.concave_le_tangent`: if `f` is concave on a real set `S`,
   both `s,t` belong to `S`, and `HasDerivAt f d s`, then
   `f t <= f s + d*(t-s)`. The proof derives the inequality from Mathlib's
   concave secant-slope inequalities on the two sides of `s`.
2. `RhCertificates.convex_negative_of_zero_and_negative_endpoint`: if `a>0`,
   `f` is convex on `[0,a]`, `f(0)=0`, and `f(a)<0`, then `f(t)<0` for
   `0<t<=a`. The coefficient `t/a` in the endpoint chord is strictly positive.
3. `RhCertificates.startup_negative_of_convex_concave`: assume
   `1/4<a<=1/2`, convexity on `[0,a]`, concavity on `[a,infinity)`, `f(0)=0`,
   `HasDerivAt f d (1/2)`, `f(1/2)<-1/40`, and `-1/32<d<0`.
   Then `f(t)<0` for every `t>0`. The existing checked arithmetic theorem
   `RhCertificates.tangent_negative` supplies the strict tangent sign.
4. `RhCertificates.startup_negative_of_second_derivative_signs`: the same
   conclusion follows if convexity and concavity are replaced by continuity
   on `[0,infinity)`, differentiability of both `f` and `deriv f` only on
   `(0,infinity)`, and `f''(x)>=0` for `0<x<a`, `f''(x)<=0` for `a<x`.
   The other transition, value and slope hypotheses remain unchanged.
5. `RhCertificates.startup_negative_of_curvature_formula`: assuming the exact
   displayed formula for `f''` on `(0,infinity)`, the transition point and its
   curvature-sign properties are derived from the independently checked
   [Curvature.lean](../../formalization/RhCertificates/Curvature.lean).
   The remaining hypotheses are continuity on `[0,infinity)`, differentiability
   of `f` and its derivative on `(0,infinity)`, `f(0)=0`, and the same value,
   derivative and slope bounds at `1/2`. The conclusion is `f(t)<0` for `t>0`.
6. Three generalized margin variants are also checked:
   `tangent_negative_of_margin`, `startup_negative_of_convex_concave_margin`,
   and `startup_negative_of_curvature_formula_margin`. They replace the narrow
   separate rational bounds by the sufficient conditions
   `f(1/2)-d/4<0` and `d<=0`. For `t>=1/4`, the tangent value is at most
   `f(1/2)-d/4`. These variants allow coarser exact numerical enclosures while
   leaving the earlier theorem APIs unchanged.

No differentiability at zero is assumed. Continuity at zero is retained to
justify the convex chord from the endpoint. Allowing `a=1/2` in the generic
theorem is valid because the full derivative at `1/2` is explicitly assumed.

## Replay and dependency audit

From the repository root:

```sh
./formalization/lakew env lean RhCertificates/StartupGeometry.lean
```

Latest direct source compilation exited successfully. The compiler's
`#print axioms` output for all eight declarations is preserved in
[startup-geometry-build.txt](../../formalization/evidence/startup-geometry-build.txt).
Every declaration depends only on `propext`, `Classical.choice`, and
`Quot.sound`; there is no `sorryAx` or added mathematical axiom. The source
uses no native computation certificate. Lean is pinned to `leanprover/lean4:v4.35.0`
and Mathlib to `56a005855ea17e0b0958f73ec801ae140b0a1679` by the committed
toolchain and manifest.

The first development compile exposed a missing algebra normalization in the
convex-combination identity. An initial curvature-wrapper compile also exposed
missing explicit arguments to Mathlib's convex-domain constructors. Both were
corrected before the successful compilation; failed drafts are not certificates.

## Independent review

The independent startup auditor checked all eight final exact statements and
their mathematical argument, including the endpoint case `a=1/2`, the curvature
wrappers and flexible margins, and independently replayed the final source.
No circular desired-sign assumption or nonstandard axiom was found. See
[the independent audit](2026-11-19-smooth-derivatives-independent-audit.md).
Kernel checking and that review are distinct evidence.

## Exact unresolved step and next test

The source currently does not instantiate `f` as the actual smooth part. The
curvature-linked theorem now replaces the assumed transition point and
curvature signs, given the exact formula
`f''(t) = -exp(t/2)+exp(-t/2)/(exp(2*t)-1)` for `t>0`.

The subsequent [derivative module](../../formalization/RhCertificates/SmoothDerivatives.lean)
now proves locally uniform summability sufficient to exchange differentiation
and summation twice for the defined smooth-part series. Its
[report](2026-11-19-smooth-derivatives-agent.md) explains that separate
kernel-checked analytic step. Together with `SmoothSeries`, it supplies the
continuity, differentiability, zero-value and curvature inputs for the defined
series. The exact value and slope bounds at `1/2`, including the intended
linear constant, still need an analytic-to-arithmetic Lean bridge.
