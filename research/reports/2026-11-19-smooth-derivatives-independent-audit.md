# Independent audit of the smooth-series differentiation bridge

## Outcome

The analytic differentiation bridge in
[SmoothDerivatives.lean](../../formalization/RhCertificates/SmoothDerivatives.lean)
passes independent mathematical review and replay. All 15 listed declarations
compile successfully using only `propext`, `Classical.choice`, and `Quot.sound`.
This genuinely proves first and second derivatives of the explicit
series-defined smooth function on the positive half-line; it does not merely
assume termwise differentiation or certify the last arithmetic step.

**Status: kernel-checked and independently reviewed** for the displayed series
with arbitrary real linear coefficient C. Identification with the original
published special-function definition and the special numerical tangent bounds
remain separate links. No RH theorem is claimed.

## Locally uniform bounds

Fix a target t>0. The proof works on the open connected interval `(t/2,infinity)`.
The derivative series is uniformly dominated there by

    exp(-rate(n)*(t/2)),

which is summable because the rates form an arithmetic progression with
positive spacing. The bound uses the checked inequalities
`0<=coefficient(n)*rate(n)<=1`. Those follow from
`coefficient(n)*rate(n)^2=1` and `rate(n)>=1`.

The source invokes the actual Mathlib termwise differentiation theorem with
this summable uniform majorant. The original series is summable at the base
point t, so the first application proves its derivative is the sum of the
individual derivatives. The derivative series is in turn summable at t, and
its individual derivatives are negative exponentials with the same summable
majorant. A second application proves its derivative is the negative
exponential-tail sum.

Every required derivative is restricted to positive arguments. There is no
assumed differentiability at zero, no circular assumption that the infinite
sum has the desired derivative, and no exchange of an improper integral with
a divergent series.

## Formula and actual derivative transfer

Combining the finite exponential/linear terms with those two series derivatives
gives

    H'(t) = -2exp(t/2)+C-sum_n coefficient(n)*rate(n)*exp(-rate(n)*t).

Differentiating again and using the checked geometric-tail identity gives

    H''(t) = -exp(t/2)+exp(-t/2)/(exp(2t)-1),  t>0.

The coefficient/rate normalization and index shift were checked in the previous
[independent audit](2026-11-19-independent-research-audit.md). The source also
transfers the derivative of the separately defined H' expression to the actual
Lean function `deriv H` by an eventual equality on the positive neighborhood.
Thus the second-derivative theorem concerns `deriv (deriv H)`, not an unrelated
formal expression carrying the same name.

The file also establishes differentiability of H and its derivative on the
positive half-line. Together with the previously proved continuity at zero,
this discharges the analytic regularity inputs of the generic curvature-based
startup geometry for this explicit series.

## Flexible-margin geometry

The final [StartupGeometry.lean](../../formalization/RhCertificates/StartupGeometry.lean)
was also independently replayed and reviewed, now with eight listed declarations.
The three new variants replace fixed numerical intervals by the exact hypotheses

    H(1/2)-d/4<0,    d<=0.

For t>=1/4 the tangent equals
`H(1/2)-d/4+d*(t-1/4)`, whose second summand is nonpositive. Hence the tangent
is strictly negative. The closed-interval chord and curvature-transition proofs
then apply as before. The altered assumptions are sufficient, with no reversed
inequality or lost endpoint. The variants do not assume the desired conclusion
for H itself.

## Replay and exact versions

Independent commands from the repository root, both exit zero:

```sh
./formalization/lakew env lean RhCertificates/SmoothDerivatives.lean
./formalization/lakew env lean RhCertificates/StartupGeometry.lean
```

Reviewed source hashes:

- SmoothDerivatives: `ecc8b4d54ecaf97604e8155af2715f3224ef796b3ee4c994a5768cc32c56efc6`
- StartupGeometry: `e5595c2f1db1f305e7cffb19cbad4f88fcc2a4955bc31af7e13d1f4ba968f1de`

The environment remains pinned by the committed Lean toolchain and dependency
manifest. The owner preserved the successful replay/axiom reports in
[smooth-derivatives-build.txt](../../formalization/evidence/smooth-derivatives-build.txt)
and [startup-geometry-build.txt](../../formalization/evidence/startup-geometry-build.txt).
No unfinished proof, added mathematical axiom, native-computation axiom or Python
certificate assumption appears in the replayed dependency lists.

## Updated unresolved step and next test

This review supersedes the pending termwise-differentiation obligation in the
previous 15-declaration SmoothSeries checkpoint. The exact remaining local
proof task is a kernel-checked tangent value/slope estimate for the relevant C,
followed by application of the generic margin geometry. A separate new constant
enclosure is being integrated and requires its own independent review; it is
not certified by this audit of the derivative bridge.

The next concrete test is to verify the finite-sum/exponential remainder bounds
and their connection to the infinite-series tangent data. After that, retain
the distinction between the explicit prime-free series and the original
special-function/prime-sum definition of g. The accumulated prime contribution
and the global RH-strength cancellation problem are not addressed by the
series regularity theorem.
