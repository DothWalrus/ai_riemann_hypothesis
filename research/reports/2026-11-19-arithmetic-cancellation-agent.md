# An arithmetic cancellation attempt using factorial floor sums

**Outcome:** the exact divisor identity for the actual von Mangoldt weights
suggests a positive-factorial comparison, but a necessary inequality for that
comparison fails. Lean verifies the obstruction for the actual kernel, including
all logarithm and square-root bounds; no numerical output is assumed.

This is a useful failed-method certificate, not a proof of RH, a new zero
verification, or a claim of mathematical novelty.

## The genuinely arithmetic input

Unlike the artificial staircases in the
[support report](2026-11-19-prime-support-agent.md), the actual von Mangoldt
weights satisfy

\[
\sum_{d\mid n}\Lambda(d)=\log n.
\]

Summing over `n <= N` and exchanging finite sums gives the exact identity

\[
\sum_{d\le N}\Lambda(d)\left\lfloor\frac Nd\right\rfloor
=\sum_{n\le N}\sum_{d\mid n}\Lambda(d)
=\sum_{n\le N}\log n
=\log(N!).
\tag{1}
\]

The divisor identity is established prior art, already formalized in the pinned
Mathlib as `ArithmeticFunction.vonMangoldt_sum`. The new Lean file replays its
sum as `mangoldt_divisor_total`; that theorem directly certifies the double
divisor sum and factorial equality. The finite reindexing to the floor form
in (1) is the ordinary written double-counting argument: a fixed `d` divides
exactly `floor(N/d)` integers in `{1,...,N}`.

For the project's prime-side expression, define

\[
w_x(d)=\frac{\log(x/d)}{\sqrt d},\qquad
S(x)=\sum_{d\le x}\Lambda(d)w_x(d).
\]

A proposed step was to express the kernel exactly as a nonnegative combination
of the floor kernels in (1):

\[
w_x(d)=\sum_{m\in T}a_m\left\lfloor\frac md\right\rfloor,
\qquad a_m\ge0,
\tag{2}
\]

at least for the prime-power arguments `d`, because all other `Lambda(d)` vanish.
For that truncated factorial reduction, require `T` to be contained in
`{0,...,floor(x)}` and match (2) at every prime power up to `floor(x)`.
Then all relevant divisors of each coefficient-support `m` occur in `S`;
interchanging the sums reduces `S` to a nonnegative combination of logarithms
of factorials. Without this support restriction, extra prime-power divisors
above `x` would need to be included and controlled separately. One-sided
factorial bounds could then be inserted without reversing inequality signs.

The next sections disprove the proposed exact positive representation.

## A necessary inequality that fails for every `x >= 32`

For every natural number `m`,

\[
\left\lfloor\frac m2\right\rfloor
\ge2\left\lfloor\frac m4\right\rfloor.
\]

Consequently every nonnegative combination in (2), regardless of its finite
index set `T`, must satisfy

\[
w_x(2)\ge2w_x(4).
\tag{3}
\]

But for the actual kernel at `x=32`,

\[
w_{32}(2)-2w_{32}(4)
=(2\sqrt2-3)\log2<0.
\]

Both 2 and 4 are genuine prime powers, so discarding the non-prime-power
constraints cannot repair this contradiction. Only elementary inequalities
`log 2 > 0` and `sqrt 2 < 3/2` are needed; there is no numerical approximation
in this proof.

More generally,

\[
w_x(2)-2w_x(4)
=\left(\frac1{\sqrt2}-1\right)\log x
 +\left(2-\frac1{\sqrt2}\right)\log2.
\]

The coefficient of `log x` is negative, so the strict violation persists for
every `x >= 32`. Lean proves this extension as
`binary_actual_weight_violation_of_large`.

Thus the first failed step is concrete: there is no exact nonnegative
floor-kernel representation matching the actual weights even at 2 and 4 in
the range where this global strategy would need it.

## Additional finite diagnostic at `x=16`

An independent finite calculation gives an obstruction already at 16 using
only the prime powers `2,3,5,8,9,13`. For `m=0,...,16`, the exact dual column

\[
D_m=\lfloor m/2\rfloor-\lfloor m/3\rfloor-\lfloor m/5\rfloor
 -\lfloor m/8\rfloor+\lfloor m/9\rfloor+\lfloor m/13\rfloor
\]

is 1 at `m=2,4,13`, 2 at `m=14`, and zero elsewhere. Hence a representation
with nonnegative coefficients supported in `0,...,16` would force

\[
F(w)=w(2)-w(3)-w(5)-w(8)+w(9)+w(13)
=a_2+a_4+a_{13}+2a_{14}\ge0.
\]

For the actual `w_16`, Lean proves `F(w_16) <= -1/100`. In particular it
proves these exact rational enclosures for the actual log/sqrt expressions:

\[
w(2)\le1.471,\quad w(3)\ge0.966,\quad w(5)\ge0.520,
\quad w(8)\ge0.245,\quad w(9)\le0.192,\quad w(13)\le0.058.
\]

The formal bounds use Mathlib's proved logarithm-series lower bounds and
geometric remainder upper bounds, followed by exact rational square-root
comparisons. No Decimal calculation is imported into Lean.

The separate standard-library diagnostic
[arithmetic_floor_probe.py](../arithmetic_floor_probe.py) independently reports
an outward interval for `F(w_16)` near `-0.01194807447` and checks the finite
floor table. Its output is reproducible in
[arithmetic_floor_result.txt](../arithmetic_floor_result.txt), but is not a
dependency of the Lean proof.

## Exact scope and the unresolved step

The obstruction concerns an **exact nonnegative representation of the kernel**.
It does not rule out:

- A positive majorant for the kernel with a rigorously controlled loss.
- Signed factorial combinations, provided both upper and lower estimates are
  used with the correct signs and their accumulated error is controlled.
- Other identities or inequalities exploiting the exact `Lambda` weights.
- Scalar identities after summing the weights that do not arise from the
  kernel representation (2).

For signed coefficients, blindly inserting a factorial upper bound reverses
the needed order at each negative coefficient. The valid comparison must use
an upper factorial bound where the coefficient is positive and a lower bound
where it is negative. No estimate for the resulting signed weighted remainder
uniformly over unbounded `x` is established here.

The exact unresolved arithmetic step is to obtain that one-sided cancellation
or to build a positive majorant whose excess is small enough for the actual
`S`/`J` sign target. Neither the divisor identity nor a plain termwise Stirling
bound supplies it. Replacing the signed remainder by an absolute envelope
would return to the previously documented loss of cancellation.

Next concrete test: formulate a signed factorial decomposition or a positive
majorant explicitly, compute its full remainder including coefficient signs,
and first prove a uniform bound for that remainder. Reject the attempt if it
merely assumes the needed `J` sign or an RH-strength moment bound.

## Verification and independent review

Status: **kernel-checked finite/kernel-representation obstruction**. The global
RH sign statement is still unproved.

Source:
[ArithmeticCancellation.lean](../../formalization/RhCertificates/ArithmeticCancellation.lean).
Build and axiom evidence:
[arithmetic-cancellation-build.txt](../../formalization/evidence/arithmetic-cancellation-build.txt).
Replay from the repository root:

```sh
./formalization/lakew env lean RhCertificates/ArithmeticCancellation.lean
PYTHONDONTWRITEBYTECODE=1 python3 research/arithmetic_floor_probe.py
```

The environment remains pinned to Lean `v4.35.0` and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. All printed declarations use only
`propext`, `Classical.choice`, and `Quot.sound`. There are no proof holes, added
mathematical axioms, or imported numerical certificates.

The relevant primary source inspected locally is the pinned Mathlib
[von Mangoldt file](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/NumberTheory/ArithmeticFunction/VonMangoldt.lean)
and its
[proved logarithm remainder bounds](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean).
An independent adversarial review of this batch is still pending at the time
of writing; agreement by agents is not a substitute for the replay above.
