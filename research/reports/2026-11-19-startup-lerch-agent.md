# Convergent Lerch-series bridge for the explicit startup formula

## Plain-language result

The special-function portion of the source formula can now be reconstructed
from its convergent defining series and proved equal to the smooth series
used in the startup certificate. The proof includes convergence at the
endpoint q=1, the first-term cancellation and the exact digamma coefficient.
This closes the previously unproved series-representation step for this
explicit reconstruction. It is not a proof of RH or a novelty claim.

**Status: kernel-checked.** Eleven public declarations in
[StartupLerch.lean](../../formalization/RhCertificates/StartupLerch.lean)
compile without warnings, using only `propext`, `Classical.choice`, and
`Quot.sound`. The new module imports no Python output or mathematical axiom.
Independent mathematical review/replay of this module is requested separately.

## Fixed defining series and convergence

Define the fixed-parameter Lerch series

\[
\Phi_*(q)=\sum_{n=0}^{\infty}\frac{q^n}{(n+1/4)^2},\qquad 0\le q\le1.
\]

This is exactly the defining series for the source's `Phi(q,2,1/4)` at the
parameters used here. No analytic continuation is required, including at q=1,
because the exponent 2 gives an absolutely convergent inverse-square series.
The formal name is `fixedPhi`; it does not assume an identity with an
independently defined general-purpose Lerch function in another library.

For every natural n, the kernel proves the uniform majorant

    norm(q^n/(n+1/4)^2) <= 16/(n+1)^2.

Indeed q^n is between zero and one, and `(n+1)^2<=16(n+1/4)^2`. The standard
p-series theorem then proves summability of the actual defined summands for
all q in the closed interval. In particular, the use of subtraction and
multiplication of the two series below is justified by summability, not by
formal manipulation of possibly divergent values.

## Exact first-term cancellation

For t>=0 let q=exp(-2t) and E=exp(-t/2). Then q lies in `(0,1]`. The source
correction is

\[
\frac{E\Phi_*(q)-\Phi_*(1)}4.
\]

Lean first represents this as the sum of the individual differences

\[
D_n(t)=\frac{E\,q^n/(n+1/4)^2-1/(n+1/4)^2}{4}.
\]

It proves summability of this exact difference sequence. The n=0 term is
`4(exp(-t/2)-1)`. For n>=0, the n+1 term is exactly the negative of the
project's `SmoothSeries.term(n,t)`, because

    exp(-t/2) * exp(-2t)^(n+1) = exp(-(2n+5/2)t).

The denominator normalization also agrees:
`4/(4n+5)^2=1/(4(n+1+1/4)^2)`. Splitting the first term of the summable series
therefore gives the kernel-checked identity

\[
\frac{E\Phi_*(q)-\Phi_*(1)}4
=4(E-1)-\sum_{n\ge0}\operatorname{term}(n,t).
\]

This proof treats t=0 explicitly through the same convergent identities;
there is no division by t or singular endpoint differentiation.

## Source expression and digamma normalization

The real reconstructed source smooth expression is defined as

\[
H_{\rm src}(t)=
-4(e^{t/2}+e^{-t/2}-2)+C_\psi t
 +\frac{e^{-t/2}\Phi_*(e^{-2t})-\Phi_*(1)}4,
\]

where `C_psi=digammaLinearCoefficient` is the real coefficient proved in
[the digamma normalization module](../../formalization/RhCertificates/StartupDigamma.lean).
That module proves both its equality to the gamma/pi/log `startupConstant`
and the reality of the complex digamma value at 1/4.

The cancellation identity and exact ring arithmetic now establish

    sourceSmoothExpression(t) = smoothPart(startupConstant,t),  t>=0.

Thus this is an identity with the actual infinite smooth series used by the
existing certificate, rather than an assumed equality between two formal names.

## Actual prime weights

The module additionally defines

    actualPrimeWeight(n) = vonMangoldt(n)/sqrt(n)

and proves `actualPrimeWeight(1)=0`. Its reconstructed `sourceFullExpression`
adds the finite prime contribution from 2 through floor(exp(t)) using those
actual weights. The theorem `sourceFullExpression_eq_fullExpression` proves
that this expression equals the previously defined full expression with the
same constant and weights for every t>=0.

The omitted n=1 source summand is zero by the proved weight lemma. The module
does not separately formalize a finite-sum reindexing theorem from a convention
that includes n=1; its full expression uses the explicit normalized cutoff
from 2. No arithmetic positivity, zero-location statement or RH premise is
needed for these equalities.

## Replay and evidence

From the repository root:

```sh
./formalization/lakew build RhCertificates.StartupDigamma
./formalization/lakew env lean RhCertificates/StartupLerch.lean
```

The final source replay exits zero. Evidence and exact environment pins are in
[startup-lerch-build.txt](../../formalization/evidence/startup-lerch-build.txt).
Development initially required building the already checked digamma dependency;
no library revision, package installation or numerical assumption was changed.

The source formula was checked against equation (1.5) and the defining-series
description of Phi on page 2 of Nakamura and Suzuki,
[On infinitely divisible distributions related to the Riemann hypothesis](https://doi.org/10.1016/j.spl.2023.109889)
(2023). This reference supplies the intended interpretation, not a new Lean axiom.

## Remaining step and next test

Independent review should check the fixed parameters, summability at q=1,
subtraction direction, n-to-n+1 index shift, n=0 cancellation, real/complex
coefficient and finite prime cutoff. The next integration test is to rewrite
the reconstructed source full expression using this equality and apply the
existing startup negativity certificate on `0<t<=log(2)`.

That result concerns the explicit formula on its startup interval. No general
Lerch analytic-continuation theorem, formal equivalence with RH, unbounded
prime-contribution estimate or novel zeta theorem is asserted.
