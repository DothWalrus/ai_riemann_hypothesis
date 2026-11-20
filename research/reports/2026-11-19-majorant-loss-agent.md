# Unavoidable loss of positive factorial-floor majorants

The [previous arithmetic attempt](2026-11-19-arithmetic-cancellation-agent.md)
ruled out exact nonnegative floor-kernel representations. This batch checks the
remaining possibility of a nonnegative floor-kernel **majorant** instead.

**Outcome:** such a majorant must overestimate the actual prime sum by a
positive amount growing proportionally to `log x`. The finite weighted loss
and its growth are kernel-checked. A separate, explicitly conditional theorem
shows that these direct majorants cannot meet a target whose permissible
margin over the true prime sum stays bounded.

This is an obstruction to a specified comparison method. It is not an RH
proof, a counterexample, a new zero-verification result, or a novelty claim.

## Exact finite definitions and hypotheses

Write

\[
w_x(d)=\frac{\log(x/d)}{\sqrt d},\quad
K(d)=\sum_{m\in T}a_m\left\lfloor\frac md\right\rfloor,
\quad a_m\ge0,
\]

where `T` is any finite set of natural numbers. For an integer `N >= 4`, define

\[
S_N(x)=\sum_{1\le d\le N}\Lambda(d)w_x(d),\qquad
P=\sum_{m\in T}a_m\log(m!).
\]

Assume only that `K(d) >= w_x(d)` at every actual prime power `d <= N`.
There is no requirement to majorize the kernel at integers where `Lambda(d)=0`.
For the project's actual truncated prime sum, take `N=floor(x)`.

Define the forced mismatch and its weighted loss by

\[
\delta(x)=2w_x(4)-w_x(2),\qquad
L(x)=(\log2)\delta(x).
\]

The Lean name `minimumLoss` denotes this proved lower bound; no optimality or
attainment assertion is intended.

## The actual von Mangoldt weighted loss

Every nonnegative floor combination obeys `K(2) >= 2K(4)`. Since the majorant
condition includes the genuine prime power 4,

\[
e_2:=K(2)-w_x(2)
\ge2w_x(4)-w_x(2)=\delta(x).
\]

At every prime power, `e_d=K(d)-w_x(d)` is nonnegative; at every other integer
its contribution is zero because `Lambda(d)=0`. Therefore, using the actual
identity `Lambda(2)=log 2`,

\[
\sum_{1\le d\le N}\Lambda(d)e_d
\ge\Lambda(2)e_2\ge L(x).
\tag{1}
\]

This is a statement about the real von Mangoldt weights, not the artificial
weights of the staircase countermodels.

The exact factorial-floor identity is now also formalized:

\[
\sum_{1\le d\le m}\Lambda(d)\lfloor m/d\rfloor=\log(m!).
\]

It follows from the pinned Mathlib Dirichlet-convolution summation theorem
`ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum`, the existing von Mangoldt
convolution identity, and `Real.sum_log_eq_log_factorial`.

If `T` is contained in `{0,...,N}`, finite reindexing gives exactly

\[
P=\sum_{1\le d\le N}\Lambda(d)K(d).
\]

For arbitrary finite `T`, this equality can gain extra prime-power terms
beyond `N`, but all those extra contributions are nonnegative. Consequently
the inequality

\[
\boxed{P-S_N(x)\ge L(x)}
\tag{2}
\]

still holds **without a coefficient-support cutoff**. Lean proves this
unrestricted version as `factorialCost_sub_primeSum_ge_minimumLoss_unrestricted`.
Thus the parent proposal's inference is correct after specifying the finite
sum and majorization conditions; extra nonnegative coefficient support does
not evade the lower bound.

## The lower bound diverges

The exact identity

\[
\delta(x)=\left(1-\frac1{\sqrt2}\right)\log x
 +\left(\frac1{\sqrt2}-2\right)\log2
\qquad(x>0)
\]

implies

\[
L(x)=\underbrace{(\log2)\left(1-\frac1{\sqrt2}\right)}_{>0}\log x
 +\left(\frac1{\sqrt2}-2\right)(\log2)^2\longrightarrow+\infty.
\]

Lean proves both the positivity of the coefficient and this limit, and also
proves `L(x)>0` for every `x>=32`. There is no sampled or numerical extrapolation
in the growth assertion.

## What the global barrier does and does not say

Let `A(x)` be a desired upper target for `S_N(x)`. Add the explicit hypothesis

\[
A(x)-S_N(x)\le B
\quad\text{eventually, for a fixed finite }B.
\tag{M}
\]

Then (2) and `L(x)->infinity` imply

\[
P>A(x)\quad\text{for every sufficiently large }x.
\]

Even the exact factorial cost eventually exceeds the target, so a valid upper
bound for that cost cannot establish the desired comparison `P<=A`. The result
allows the coefficients and their finite index sets to vary arbitrarily with
`x`. No continuity or fixed-dimension assumption is imposed on those choices.

`positive_factorial_majorants_fail` is the combined conditional Lean theorem:
it explicitly assumes eventual nonnegative coefficients, kernel majorization
at actual prime powers, `N(x)>=4`, and the bounded permissible margin (M).
It then concludes `A(x)<P(x)` eventually. It has no RH assumption or hidden axiom.

For the project's archimedean comparison, write `g(log x)=H(log x)+S(x)` and
`A(x)=-H(log x)`. Then `A(x)-S(x)=-g(log x)`.

**External analytic bridge, not certified by this batch:** under RH the
zero expansion makes `g` bounded. If that implication and the exact `g/H/S`
identification are supplied, (M) follows and the barrier applies to this
particular direct positive-floor-majorant route. These analytic statements
are not imported into Lean as axioms or silently treated as proved here.
The [zero-tail note](../notes/zero-tail.txt) gives the project's zero-expansion
context; the actual analytic bridge still needs a separate formalization.

This does not rule out signed factorial combinations, compensating arithmetic
correction terms, different positive kernel families, or arguments that never
try to compare this componentwise majorant's full cost directly to `A`.
It does not establish any new sign statement for the actual `g`.

## Replay, scope, and next test

Source: [MajorantLoss.lean](../../formalization/RhCertificates/MajorantLoss.lean).
Evidence: [majorant-loss-build.txt](../../formalization/evidence/majorant-loss-build.txt).

- The finite actual-weight loss (2), factorial reindexing, and divergent lower
  bound are **kernel-checked**.
- The bounded-margin global method barrier is **conditional kernel-checked**;
  (M) is an explicit hypothesis.
- The RH-to-bounded-margin analytic bridge is **not yet formalized here**.

Replay from the repository root:

```sh
./formalization/lakew build RhCertificates.ArithmeticCancellation
./formalization/lakew env lean RhCertificates/MajorantLoss.lean
```

The environment remains Lean `v4.35.0`, Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`. All printed declarations use only
`propext`, `Classical.choice`, and `Quot.sound`. No numerical data, proof holes,
or extra mathematical axioms are used. The source for the finite arithmetic
reindexing was inspected at the pinned
[Mathlib arithmetic-function file](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/NumberTheory/ArithmeticFunction/Misc.lean).

The first unresolved proof step remains cancellation outside this positive
floor cone. The next concrete test is to write a signed factorial decomposition
with every remainder and sign exposed, or identify a different kernel family
that avoids the forced 2-versus-4 weight mismatch. Merely tuning the existing
nonnegative coefficients cannot remove (2).

Independent adversarial review of this new batch is pending at report
preparation; the successful exact-source replay is evidence of kernel checking,
not a claim that every proposed analytic application has been verified.
