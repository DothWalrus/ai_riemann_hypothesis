# Independent audit of the positive factorial-majorant loss

## Outcome and verification levels

The exact [MajorantLoss.lean](../../formalization/RhCertificates/MajorantLoss.lean)
source with SHA256
`3bb2ff5b074e2e78dfdc91c6837a057f0de8d54f797e0e3a7876ee7a22144e16`
passed independent mathematical review and source replay. All sixteen printed
declarations compiled with the standard three logical axioms only.

- The actual von Mangoldt weighted finite loss, factorial reindexing and
  divergence of its lower bound are **kernel-checked**.
- The conclusion that a direct majorant eventually exceeds a target with
  bounded permissible margin is **conditional kernel-checked**, with that
  bounded-margin condition explicitly stated.
- An RH-to-bounded-margin application to the analytic screw function is
  **not formalized by this module**.

No novelty, RH proof or counterexample is claimed. The name `minimumLoss`
denotes a proved lower bound, not a claimed optimal minimum or an attained
infimum.

## Exact finite loss and the actual arithmetic weights

Let `K(d)=sum_{m in T} a_m*floor(m/d)`, with arbitrary finite support `T` and
nonnegative coefficients. Let `w_x(d)=log(x/d)/sqrt(d)`. The binary floor
inequality gives `K(2)>=2*K(4)`. If `K(4)>=w_x(4)`, then

\[
K(2)-w_x(2)\ge\delta(x):=2w_x(4)-w_x(2).
\]

The majorization hypotheses are required only at prime powers in the finite
prime-sum domain. Those are exactly the arguments where the actual von
Mangoldt weight may be nonzero. The proof uses its established nonnegativity,
vanishing at non-prime-powers, and the exact identity `Lambda(2)=log(2)`.
Thus every weighted excess term is nonnegative, and extracting its `d=2`
term gives the lower bound `L(x)=log(2)*delta(x)`. Membership of both 2 and 4
in the finite domain is explicitly supplied.

This is a statement about the actual arithmetic weights, not an artificial
positive staircase or a presumed spectral measure.

## Factorial cost and unrestricted coefficient support

The floor-sum identity

\[
\sum_{1\le d\le m}\Lambda(d)\lfloor m/d\rfloor=\log(m!)
\]

is now proved in Lean from Mathlib's arithmetic-function convolution summation
identity. This fills the finite reindexing that the earlier arithmetic module
had left as a written argument.

When each `m in T` is at most `N`, reindexing proves equality between the
factorial cost and the weighted floor-kernel cost through `N`. For unrestricted
finite `T`, the source extends the domain to `M=N+sup(T)`. The extra weighted
terms are nonnegative, so the truncated cost through `N` is at most the full
factorial cost. The lower loss bound therefore remains valid without a support
cutoff. The proof does not silently assume that all coefficients have indices
below the prime-sum truncation.

The cases `m=0` and empty `T` cause no exception: `log(0!)=0` and the relevant
positive-divisor floor terms vanish. All summations are finite.

## Divergence and the conditional eventual barrier

For `x>0`, the exact mismatch identity is

\[
\delta(x)=(1-1/\sqrt2)\log x+(1/\sqrt2-2)\log2.
\]

The coefficient `log(2)*(1-1/sqrt(2))` is strictly positive, so the checked
lower bound `L(x)` tends to positive infinity. This is an analytic limit in
Lean, not an extrapolation from finite samples. Positivity for `x>=32` is
also checked.

The final comparison assumes a single real bound `B` such that
`A(x)-S(x)<=B` eventually, and assumes `P(x)-S(x)>=L(x)` eventually.
Once `L(x)>B`, these inequalities imply `P(x)>A(x)`. The quantifier over `B`
is a fixed constant; it is not an unrestricted function of `x`.

The combined factorial theorem allows the finite support and nonnegative
coefficients to vary arbitrarily with `x`. It requires eventual majorization
at actual prime powers and eventual `N(x)>=4`. Its unrestricted version has
no bound on the coefficient indices. The bounded permissible margin remains
an explicit hypothesis: the source does not claim it for the actual screw
function without a separate analytic proof.

## Independent replay and dependency audit

```sh
./formalization/lakew env lean RhCertificates/MajorantLoss.lean
```

Exit status was zero with no warnings. Every printed declaration has exactly
`propext`, `Classical.choice`, and `Quot.sound` in its axiom report; no `sorryAx`,
added mathematical axiom or native-computation axiom occurs. Evidence is in
[majorant-loss-independent-replay.txt](../../formalization/evidence/majorant-loss-independent-replay.txt).
The project pins Lean `leanprover/lean4:v4.35.0` and Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

## Exact remaining step and next test

The finite weighted loss does not need RH. Applying the eventual comparison
barrier to the project's archimedean target still requires the precise
`g/H/S` identification and a justified bounded-margin statement. The report
correctly retains that application as a separate analytic bridge.

An alternative cancellation method must expose how it avoids this growing
loss, for example by signed coefficients with both inequality directions and
all remainders controlled, or by a different kernel family. This result does
not rule out those alternatives, nor does it prove a new sign statement for
the full screw function.
