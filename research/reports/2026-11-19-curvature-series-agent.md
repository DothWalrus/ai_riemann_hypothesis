# Exact curvature and endpoint continuity for the startup argument

The startup argument needs a change from convexity to concavity and continuity
at zero. This work puts those pieces into Lean for the displayed smooth series.
It does not prove RH or establish the global sign of the full screw function.
No novelty is claimed.

## Results and verification level

The following statements are **kernel-checked**, with pinned Lean 4.35.0 and
Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`:

- The cubic `P(y)=y^3-y-1` is strictly increasing for `y>=1`.
- For `t>0`, the expression
  `F(t)=-exp(t/2)+exp(-t/2)/(exp(2t)-1)` has the opposite sign to `P(exp(t))`.
- There exists `a` strictly between `1/4` and `1/3` such that `F(t)>=0` for
  `0<t<=a` and `F(t)<=0` for `t>=a`.
- For every real linear coefficient `C`, the explicitly defined series

  `H_C(t)=-4(exp(t/2)-1)+C*t-sum_{k>=1}(1-exp(-(2k+1/2)t))/(4(k+1/4)^2)`

  converges for `t>=0`, is continuous on `[0,infinity)`, and has `H_C(0)=0`.
- Each tail summand has the expected first and second derivatives. The second
  derivative is exactly `-exp(-(2k+1/2)t)` because its coefficient times the
  squared exponential rate is 1.
- For `t>0`, the exponential second-derivative tail is summable and equals
  `exp(-t/2)/(exp(2t)-1)`, by an exact geometric-series computation.

The curvature theorem concerns the explicit exponential expression `F`; by
itself it does not assert that `H_C''=F`. The series theorem defines `H_C`
directly; it does not import the published Lerch formula or prove its identity
with the full screw function. These distinctions remain essential when applying
the generic [startup geometry](../../formalization/RhCertificates/StartupGeometry.lean).

## Proof details

In [Curvature.lean](../../formalization/RhCertificates/Curvature.lean), the
curvature is put over the positive denominator
`exp(t/2)*(exp(t)^2-1)`, with numerator `-P(exp(t))`. Cubic monotonicity follows
from factoring its difference at two points. An exact Taylor bound from Mathlib
proves `exp(1/4)<13/10`; then `P(13/10)<0`. The elementary lower bound
`exp(1/3)>=4/3` and `P(4/3)>0` gives the other endpoint. The intermediate value
theorem supplies the transition. No Python values are assumed in this proof.

In [SmoothSeries.lean](../../formalization/RhCertificates/SmoothSeries.lean),
natural index `n=0` corresponds to written index `k=1`. Its coefficient is
`4/(4*(n+1)+1)^2`, formally shown equal to the written coefficient. For `t>=0`
each summand is nonnegative and bounded by `1/(n+1)^2`. The summable majorant
and Mathlib's uniform-series continuity theorem justify continuity at zero,
even though a derivative at zero need not exist. Termwise derivative identities
are separate from differentiating the infinite sum.

## Replay and evidence

From the repository root:

```sh
./formalization/lakew env lean RhCertificates/Curvature.lean
./formalization/lakew env lean RhCertificates/SmoothSeries.lean
./formalization/lakew build +RhCertificates.Curvature +RhCertificates.SmoothSeries
```

The successful source recompilations and axiom reports are in
[curvature-build.txt](../../formalization/evidence/curvature-build.txt) and
[smooth-series-build.txt](../../formalization/evidence/smooth-series-build.txt).
Every printed declaration uses only `propext`, `Classical.choice`, and
`Quot.sound`. No unfinished proof, added mathematical axiom, native computation
certificate, or Python-generated premise was used. Development compilation
errors were corrected before these successful logs were recorded.

The [axiom checker](../../scripts/check_axiom_report.py) now accepts explicit
declaration names through repeatable `--theorem` options. Its default remains
the original tangent lemma. All seven checker tests pass, including rejection
of missing declarations and duplicate reports containing `sorryAx`. Checking an
axiom report does not verify the correspondence between prose and a theorem;
independent statement review is still required.

The curvature and series proofs use the pinned Mathlib primary source for
exponential bounds, intermediate values, p-series summability and continuity
of uniformly dominated function series. These sources were inspected locally.

## Independent review and remaining step

An independent agent is reviewing the curvature and startup statements. Treat
that review separately from the successful kernel checks; no global proof is
inferred from either.

The next analytic obligation is to justify differentiation of the infinite
series locally on `t>0` and connect the already summed second-derivative tail
to `F`. Individual summand derivatives alone do not discharge that
obligation. The numerical inequalities for `H_C(1/2)` and `H_C'(1/2)`, with the
actual Euler/digamma coefficient `C`, also still need an analytic-to-Lean
certificate. Finally, the written prime-free identity with the actual screw
function must be formalized. Even completing those finite startup tasks leaves
the accumulated prime contribution for unbounded `t` unresolved.
