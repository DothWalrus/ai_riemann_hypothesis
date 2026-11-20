# Independent audit of the arithmetic floor-kernel obstruction

## Outcome and verification level

[ArithmeticCancellation.lean](../../formalization/RhCertificates/ArithmeticCancellation.lean)
and [its report](2026-11-19-arithmetic-cancellation-agent.md) pass independent
mathematical review and compiler replay. The finite-support condition
discussed below is now explicit in the owner report. The 13 printed declaration reports use only `propext`,
`Classical.choice`, and `Quot.sound`.

**Status: kernel-checked and independently reviewed for the stated exact
nonnegative kernel-representation obstruction.** It is a certificate that one
specific attempted method fails. It does not prove or disprove RH, bound the
actual prime-side expression globally, or claim mathematical novelty.

## Arithmetic input and a finite-support clarification

The already established von Mangoldt divisor identity is used correctly.
Summing it over the positive integers through N gives the double-divisor sum
identity with log(N!), which is the exact statement compiled in the new file.
Reindexing that double sum into the floor form remains written finite
combinatorics, as the report explicitly acknowledges.

There is one condition worth stating whenever using such a representation to
reduce the truncated prime sum S(x) to factorial values: the coefficient indices
m must be at most floor(x), or an appropriate zero-extension/full-sum identity
must be supplied. Matching a kernel only at d<=x while allowing m>x could add
extra von Mangoldt contributions from x<d<=m to log(m!). This condition was
reported to the proof owner and has been added explicitly to the report.
It does not affect the proved
obstruction: the binary obstruction already rules out matching the two required
kernel values for **any** finite index support, a stronger statement than the
restricted-support method would need.

## The two-prime-power obstruction

For every natural m, floor(m/2)>=2floor(m/4). Multiplication by nonnegative
coefficients and finite summation preserve this inequality. Hence any exact
nonnegative combination of floor kernels must have w(2)>=2w(4).

For the actual kernel w_x(d)=log(x/d)/sqrt(d), the difference at x=32 is

    w_32(2)-2w_32(4)=(2sqrt(2)-3)log(2)<0.

The elementary square-root and logarithm inequalities are correct, and both
arguments 2 and 4 are genuine prime powers within the cutoff. Thus omitting
non-prime-power constraints cannot repair the contradiction.

The general difference is affine in log(x), with negative coefficient
`1/sqrt(2)-1`. Its value is already negative at 32, so it remains negative for
all x>=32. The formal extension uses exactly this monotonicity and correctly
requires x positive when expanding log(x/d).

No numerical interval is needed by this binary argument. It permits arbitrary
finite coefficient support, not just m<=x.

## The additional x=16 certificate

The six-row dual vector at d=2,3,5,8,9,13 was checked independently. For
m=0,...,16, the floor-column combination is 1 at m=2,4,13, 2 at m=14, and
zero elsewhere. Nonnegative coefficients therefore make the dual combination
of represented weights nonnegative.

The bounds on the six actual log/sqrt weights have the correct directions:
upper bounds are used at positive dual coefficients and lower bounds at
negative coefficients. Their exact rational combination is at most -1/100.
The source proves those enclosures with Mathlib logarithm-series remainder
bounds and rational square-root comparisons; it does not import the Python
interval diagnostic as an assumption. The reciprocal inequalities all use
positive square-root denominators correctly.

This is a finite-support certificate at x=16. The two-prime-power result is the
separate argument supplying the stronger obstruction for all x>=32.

## Scope limits

The checked statements rule out an **exact nonnegative representation** of the
specified kernel. They do not rule out a positive majorant with controlled
excess, signed combinations with correctly directed factorial bounds, scalar
identities that hold only after summation against Lambda, or another arithmetic
identity. The agent report preserves these distinctions.

A signed representation would require an upper factorial estimate for positive
coefficients and a lower estimate for negative coefficients. Replacing every
factorial by an upper bound would reverse the inequality at negative weights.
No signed remainder estimate sufficient to control unbounded x is proved here.

## Independent replay and remaining step

Independent command from the repository root, exit zero:

```sh
./formalization/lakew env lean RhCertificates/ArithmeticCancellation.lean
```

Reviewed source SHA-256:
`7833f528476f2849761e8597a12efc0f1e005c950d600cda9d0958235989bd4d`.
The owner's evidence is
[arithmetic-cancellation-build.txt](../../formalization/evidence/arithmetic-cancellation-build.txt).
The pins remain the committed Lean toolchain and Mathlib manifest.

No unfinished proof, added mathematical axiom, native-computation axiom, or
assumed numerical enclosure occurs in the final actual-kernel obstruction.
The first unresolved arithmetic step is still a one-sided cancellation estimate
for the actual von Mangoldt weights. The next concrete test is an explicitly
stated signed decomposition or controlled-loss majorant, including its full
remainder, without assuming the desired J sign.
