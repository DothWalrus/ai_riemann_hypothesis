# Signed factorial attempt: exact remainder, no global cancellation bound

**Status: failed global proof attempt.** The signed decomposition is exact, but
the estimates obtained here do not improve the known one-sided `J` bounds.
The formal output is a finite summation-by-parts identity and actual Stirling
remainder facts. No RH proof, new equivalent criterion, or novelty is claimed.

## Exact finite coefficients

Fix `x>1`, `N=floor(x)`, and `w_x(d)=log(x/d)/sqrt(d)` for `1<=d<=N`.
With the actual integer Möbius function `mu`, set

\[
b_d=\sum_{j\le N/d}\mu(j)w_x(jd),\qquad
a_m=b_m-b_{m+1}\quad(1\le m\le N).
\]

Here `b_(N+1)=0`. Finite summation by parts gives

\[
\sum_{m\le N}a_m\lfloor m/d\rfloor=\sum_{j\le N/d}b_{jd}=w_x(d)
\quad(1\le d\le N).
\]

For the last equality, substitute `b`, group the finite pairs with product
`r=jk`, and use `sum_{k|r}mu(k)=1` for `r=1` and zero otherwise. No infinite
series or continued integral is used. The domain `d<=N` matters: the actual
untruncated kernel need not vanish beyond `N`.

The factorial-floor identity from the
[majorant report](2026-11-19-majorant-loss-agent.md) then yields exactly

\[
S(x)=\sum_{m\le N}a_m\log(m!).
\]

The general finite Möbius inversion derivation above is a **written argument,
not yet fully Lean-certified**. The exact coefficient definitions and terminal
zero boundary are present in the new Lean file.

## The concrete signed cancellation term

Let `F_m=log(m!)`, `M_0=r_0=0`, and for `m>=1` use the standard smooth term

\[
M_m=(m+\tfrac12)\log m-m+\tfrac12\log(2\pi),\qquad r_m=F_m-M_m.
\]

Thus `S=Q_x+R_x`, where `Q_x=sum a_m M_m` and

\[
R_x=\sum_{m\le N}a_mr_m
=b_1r_1+\sum_{m=2}^N b_m(r_m-r_{m-1}).
\tag{R}
\]

The exact rearrangement (R), including its boundary terms, is **kernel-checked**
for the explicitly defined finite coefficients.

The actual remainder is nonnegative and decreasing for `m>=1`. Crucially,
the step bound used here is the proved Robbins **stepwise** bound

\[
0\le r_{m-1}-r_m\le\frac1{12(m-1)m}\quad(m\ge2),
\]

obtained directly from pinned Mathlib's `Stirling.log_stirlingSeq_sdiff_le`.
It is not inferred by subtracting separate upper bounds on `r_m`.
Both the step bound and its nonnegative sign are independently replayed in Lean.

## What a safe absolute estimate gives

For `y>=1`, the function `log(y/u)/sqrt(u)` is nonnegative and decreasing
on `[1,y]`. A sum-integral comparison and `|mu(j)|<=1` give

\[
|b_m|\le\frac4m\sqrt x\qquad(1\le m\le N).
\]

Indeed, the corresponding sum over all integer `j<=y=x/m` is at most
`log y + integral_1^y log(y/u)/sqrt(u) du
=4 sqrt(y)-log y-4 <=4 sqrt(y)`.
Applying the true step bound to (R) gives the safe estimate

\[
|R_x|\le4\sqrt x\,r_1+
 \frac{\sqrt x}{3}\sum_{m=2}^N\frac1{m^2(m-1)}
\le(4r_1+\tfrac13)\sqrt x,
\qquad r_1=1-\tfrac12\log(2\pi).
\]

This elementary absolute estimate is a **written argument**, not a full Lean
formalization of the sum-integral comparison. It is square-root sized and
does not supply the sought one-sided cancellation. The smooth part `Q_x`
still contains signed Möbius sums as well. Thus this calculation establishes
no improved global estimate for the actual `S`, `J`, or `g`.

One must not assume that a separately requested strong bound for
`B(y)=sum_{j<=y}mu(j)j^(-1/2)log(y/j)` is harmless. Initially for `Re s>1/2`,
ordinary absolutely convergent integration gives

\[
\int_1^\infty B(y)y^{-s-1}\,dy=\frac1{s^2\zeta(s+1/2)}.
\]

A uniform subpower bound on `B` would already force this transform to be
holomorphic in `Re s>0` and exclude the missing right-of-critical-line zeros.
It would therefore insert RH-strength cancellation rather than derive it.
This observation diagnoses a forbidden shortcut; it is not a new criterion
offered as progress. No continued Mellin value is substituted for an ordinary
convergent sum or integral in this attempt.

## Normalization and the exact unresolved step

Because `Lambda(1)=0` and `log(1!)=0`, the coefficient `a_1` is free for the
actual factorial cost. Changing it shifts `Q_x` and `R_x` by opposite amounts.
Lean explicitly checks that the smooth and remainder contributions at 1 cancel.
Thus the isolated remainder is not an invariant of all signed representations;
the bound above concerns the stated canonical choice. It is not an obstruction
to every possible signed approach.

The unresolved step is a new one-sided estimate for the **combined** signed
smooth and remainder terms. Restating `Q_x+R_x<=-H(log x)` would only restate
the original sign problem. No such estimate is proved here.

Next test: fix the irrelevant unit coefficient, for example `a_1=0`, expose the
remaining weighted Möbius cancellation and all smooth/remainder signs, and
identify an arithmetic estimate that was not already equivalent in strength
to the missing zero-free half-plane. Until such an estimate is proved, this
signed-factorial decomposition is an exact rewriting with no global gain.

## Formal replay and limits

Source: [SignedFactorial.lean](../../formalization/RhCertificates/SignedFactorial.lean).
Evidence: [signed-factorial-build.txt](../../formalization/evidence/signed-factorial-build.txt).

```sh
./formalization/lakew build RhCertificates.ArithmeticCancellation
./formalization/lakew env lean RhCertificates/SignedFactorial.lean
```

The coefficient definitions, terminal boundary, exact finite remainder identity,
unit cancellation, and actual Stirling positivity/step facts are kernel-checked.
The full finite Möbius inversion, displayed crude square-root estimate, and
analytic diagnostic transform are written derivations, **not Lean certificates**.
No unproved cancellation statement is added as a mathematical axiom.

The environment is pinned to Lean `v4.35.0` and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`; all printed declarations use only
`propext`, `Classical.choice`, and `Quot.sound`. The primary
[Mathlib Stirling source](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/SpecialFunctions/Stirling.lean)
and Möbius source were inspected locally at that revision. Independent review
of the new written derivations remains pending.
