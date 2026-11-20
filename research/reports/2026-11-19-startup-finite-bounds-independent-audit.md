# Independent audit of finite startup value and slope bounds

## Outcome

The exact source [StartupFiniteBounds.lean](../../formalization/RhCertificates/StartupFiniteBounds.lean)
passed an independent mathematical review and compiler replay. All ten listed
declarations compiled with only the three standard logical axioms.

**Verification level: kernel-checked inequalities for the defined series, with
explicit intervals for its linear coefficient.** No Python result or unproved
decimal enclosure is used as a mathematical premise. This is a finite startup
certificate, not a proof of RH; no novelty is claimed.

## Exact results

For the defined series `H_C` and its checked derivative expression `D_C`:

\[
C\le2691/1000\quad\Longrightarrow\quad H_C(1/2)<-1/50,
\]

\[
67/25<C<2691/1000\quad\Longrightarrow\quad
-1/25<D_C(1/2)<0.
\]

The earlier derivative module proves that `D_C(1/2)` is the actual derivative
of `H_C` at `1/2`. The separate constant-bound certificate proves this interval
for the exact Euler-gamma/pi/logarithm constant in the written formula. These
are explicit links, rather than an assumption that a floating-point value is
the derivative of the intended infinite sum.

The two inequalities imply the sufficient flexible tangent margin
`H_C(1/2)-D_C(1/2)/4<0`: the right side is less than `-1/50+1/100=-1/100`.

## Independent mathematical checks

1. Six-term exponential Taylor estimates enclose `exp(1/4)` between
   `321/250` and `12841/10000`. Taking positive reciprocals reverses the
   inequalities correctly, enclosing `exp(-1/4)` between `10000/12841`
   and `250/321`.
2. The exact exponent identity is
   `exp(-rate(n)/2)=exp(-1/4)^(4*n+5)`. Its index starts at the written
   `k=1` term, so there is no off-by-one error in the tail.
3. Every original series summand at `1/2` is nonnegative. Dropping the
   infinite tail therefore produces an upper bound on `H_C(1/2)`, because
   that series is subtracted. The first sixteen summands exceed `23/100`
   by a kernel-checked rational comparison. Together with the lower
   exponential bound and upper coefficient bound, this proves the stated
   value inequality in the correct direction.
4. The derivative-series coefficient is exactly `2/(4*n+5)`. Its first two
   nonnegative summands give a strict lower bound `13/100` for the whole
   derivative-series sum.
5. For the upper bound, the shifted tail index `n+2` has coefficient at most
   `2/13`. With `X=250/321`, its exponential factor is bounded by
   `X^13*(X^4)^n`. Since `0<X^4<1`, the infinite majorant sums to
   `(2/13)*X^13/(1-X^4)`. Adding the separately bounded first two terms
   proves the complete derivative-series sum is strictly less than `3/20`.
   Thus the tail is actually controlled; it is not dropped in an invalid
   upper bound.
6. The final derivative inequalities follow by linear arithmetic from those
   bounds and the stated `C` interval. The strictness needed by the tangent
   margin is retained.

## Independent replay and axiom audit

```sh
./formalization/lakew env lean RhCertificates/StartupFiniteBounds.lean
```

Exit status was zero. All ten declarations have exactly `propext`,
`Classical.choice`, and `Quot.sound` in their dependency lists. There is no
`sorryAx`, native-computation axiom or added mathematical axiom. Two source
locations emitted nonfatal tactic-style linter warnings; they did not affect
the proof check. Evidence is saved in
[startup-finite-bounds-independent-replay.txt](../../formalization/evidence/startup-finite-bounds-independent-replay.txt).

The environment pins Lean `leanprover/lean4:v4.35.0` and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

## Remaining step and next test

The immediate next test is an exact integration theorem: instantiate these
bounds with `startupConstant`, combine them with the series derivative and
curvature theorems, and apply the margin geometry. Then transfer that result
through the checked vanishing finite prime contribution on `0<t<=log(2)`.

An identification with the originally published special-function definition
must remain explicit. None of these local estimates bounds the accumulated
prime contribution for arbitrarily large arguments.
