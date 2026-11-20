# Explicit countermodels to a prime-error-bound deduction

The question was whether normalization, monotonicity, and a classical
prime-number-theorem-shaped absolute error estimate can force the eventual
inequality `J(x) <= 0` needed by the
[Chebyshev-error reduction](../notes/chebyshev-error.txt).

**Outcome:** those inputs alone cannot do that. An explicit artificial function
satisfies all those inputs but has a positive weighted error integral. A second,
written construction preserves the locations and positivity of prime-power
jumps while changing their weights. Neither construction is Chebyshev's
function, a zeta zero, or a counterexample to RH. No novelty is claimed.

## The exact obstruction and verification level

For `x >= 1`, define

\[
\widetilde\psi(x)=x+x^{3/4}-2,\qquad
\widetilde E(x)=\widetilde\psi(x)-x=x^{3/4}-2,
\]

and use the same weighted-error kernel as the project:

\[
\widetilde J(x)=\int_1^x\widetilde E(u)u^{-3/2}
 \left(1+\tfrac12\log(x/u)\right)\,du.
\]

The following facts hold:

1. `psi_tilde(1)=0`, and `psi_tilde` is nonnegative and increasing on `[1,infinity)`.
2. `|E_tilde(x)| <= x^(3/4)`, so `psi_tilde(x)/x -> 1`.
3. For every `c >= 0`, if `log(x) >= 16 c^2`, then
   `|E_tilde(x)| <= x exp(-c sqrt(log x))`.
4. `J_tilde(exp(t)) = 12 exp(t/4)-12-4t` for every `t >= 0`, and this is
   strictly positive for `t >= 6`.

The exact logarithmic-coordinate statements, including the interval-integral
identity and positivity, are **kernel-checked** in
[PrimeObstruction.lean](../../formalization/RhCertificates/PrimeObstruction.lean).
The source uses `modelPsi(t)=exp(t)+exp(3t/4)-2`, and proves monotonicity,
normalization, nonnegativity, the absolute and relative error bounds, the explicit
PNT-shaped envelope, and the model-to-integral convolution identity. The ordinary
change of variables `u=exp(v)` connecting the displayed `x` notation to that
logarithmic-coordinate definition is written here, not separately formalized.

This certifies an obstruction to a proposed deduction. It does not certify
any new statement about the actual Chebyshev function or RH.

## Derivation

For `x >= 1`, `x^(3/4) >= 1`, so

\[
-x^{3/4}\le x^{3/4}-2\le x^{3/4}.
\]

After dividing by `x`, the absolute relative error is at most `x^(-1/4)`.
For the PNT-shaped bound put `v=sqrt(log x)`. The condition `v >= 4c` gives
`3v^2/4 <= v^2-cv`, and exponentiation gives item 3. This is a bound for
every fixed `c`, not just one selected constant.

Writing `x=exp(t)` and `u=exp(v)` gives

\[
\widetilde J(e^t)=\int_0^t
 \left(e^{v/4}-2e^{-v/2}\right)
 \left(1+\tfrac12(t-v)\right)\,dv.
\]

A primitive, with `t` held fixed, is

\[
F_t(v)=e^{v/4}(12+2t-2v)-2(v-t)e^{-v/2}.
\]

Its derivative is exactly the integrand. Since `F_t(t)=12 exp(t/4)` and
`F_t(0)=12+4t`, item 4 follows. Lean proves the derivative and applies the
fundamental theorem of calculus to the actual interval integral; it does not
load a Python result or assume the integral identity.

For the sign, `exp(t/8) >= 1+t/8`, so for `t >= 0`,

\[
e^{t/4}=\left(e^{t/8}\right)^2\ge(1+t/8)^2,
\qquad
\widetilde J(e^t)\ge\frac{t(3t-16)}{16}>0\quad(t\ge6).
\]

The positive error is small relative to the main term, yet the kernel has
positive weight and retains that bias. An absolute error envelope says nothing
about the one-sided cancellation required for eventual negativity.

## Follow-up: retaining prime-power jump locations

This subsection is a **written argument, not a complete Lean formalization**
of the staircase construction. Its integral-comparison component has a separate
conditional Lean theorem described below. It shows why even the locations of
the jumps would not suffice without the correct arithmetic weights.

Let `q_+(x)` be the least prime power strictly greater than `x`. Define

\[
\Psi(x)=\begin{cases}
0,&1\le x<2,\\
q_+(x)+2,&x\ge2.
\end{cases}
\]

This is a nonnegative, nondecreasing, right-continuous step function with
`Psi(1)=0`. Its first jump at 2 has size 5; subsequent jumps at a prime power
`q_i` have size `q_(i+1)-q_i`, which is positive. Thus its jump locations are
genuine prime powers, but its weights are **not** `Lambda(n)`. In particular,
this is not the actual Chebyshev function and does not preserve the zeta Euler
product or its exact logarithmic-derivative coefficients.

Its error `E_Psi(u)=Psi(u)-u` equals `-u` before 2 and is at least 2 afterward.
For `t >= log 2`, positivity of the weighting kernel therefore gives

\[
J_\Psi(e^t)\ge t+4-4\sqrt2.
\]

To check the constant, compare with the lower error `-u` on `[1,2)` and `2`
on `[2,infinity)`. In logarithmic coordinates the two integrals have primitives
`exp(v/2)(v-t-4)` and `2(v-t)exp(-v/2)` respectively. Their boundary values sum
to `t+4-4 sqrt(2)`. The lower bound is positive, for example, at every `t >= 6`.

The same construction is compatible with a classical PNT-shaped error envelope
under the following explicit input for the **actual** Chebyshev function:

\[
|\psi(y)-y|\le C y e^{-c\sqrt{\log y}}
\quad\text{for all sufficiently large }y,\qquad C,c>0.
\tag{P}
\]

Here (P) is treated as a stated external premise; this report does not reprove
or formalize a PNT error theorem. Let
`h=4Cx exp(-c sqrt(log x))`. Eventually `h <= x`. If there were no prime power
in `(x,x+h]`, actual `psi` would be constant there. But (P) gives

\[
\psi(x+h)-\psi(x)\ge h-C(x+h)e^{-c\sqrt{\log(x+h)}}
  -Cx e^{-c\sqrt{\log x}}
\ge Cx e^{-c\sqrt{\log x}}>0,
\]

a contradiction. Hence `q_+(x)-x <= h` eventually, and

\[
0<E_\Psi(x)\le4Cx e^{-c\sqrt{\log x}}+2.
\]

Since `x exp(-c sqrt(log x))` tends to infinity, the additive 2 is absorbed
by a constant. The staircase therefore has the same shape of asymptotic
envelope and `Psi(x)/x -> 1`, while its `J` is eventually positive.

The implication using the exact `Lambda` weights remains untouched. This
argument does not establish that adding correct support or weights would be
sufficient for a successful global proof; it only rules out discarding those
weights and retaining the listed coarse information.

## Lean scope, replay, and review

The pinned environment is Lean `v4.35.0`, Mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Replay from the repository root:

```sh
./formalization/lakew env lean RhCertificates/PrimeObstruction.lean
```

The build and axiom report are preserved in
[prime-obstruction-build.txt](../../formalization/evidence/prime-obstruction-build.txt).
The successful theorem reports use only `propext`, `Classical.choice`, and
`Quot.sound`. There are no `sorry`/`admit`, added mathematical axioms, or native
computation certificates. Compilation failures during development were resolved;
only a successful final build counts as verification.

`weightedError_lower_of_surplus` is a **conditional kernel-checked** theorem
for arbitrary logarithmic-coordinate inputs. It assumes interval integrability,
nonnegativity of the input before a cutoff `a`, and a surplus of at least
`exp(a)` over `exp(v)` after the cutoff. It proves
`weightedError >= t+4-4 exp(a/2)` by integral comparison. Instantiating `a=log 2`
with the staircase requires its measurability/integrability and pointwise
properties; those links and the next-prime-power construction are not yet
formalized here.

The parent independently recomputed the smooth-model convolution identity.
A separate adversarial review of all statements and Lean scope is still needed;
agent agreement alone is not a mathematical certificate.

The formal proof uses the pinned Mathlib primary source for
[real exponential derivatives](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean)
and the
[fundamental theorem of calculus](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean).
Those sources were inspected locally at the pinned revision. The project
Chebyshev-error note supplies the definition of `J`; no additional zeta theorem
is used to prove the smooth-model obstruction.

## Exact unresolved step and next test

The unresolved RH-strength step is still a one-sided cancellation estimate for
the **actual** `Lambda` weights, such as eventual `J(x) <= 0` or the one-sided
subpower upper bound in the Chebyshev-error note. Neither model supplies it.

Next test: independently audit the prime-power staircase argument, then encode
its locally finite step function and its integrability in Lean to instantiate
the conditional comparison lemma. For a proof attempt about actual primes,
require the next proposed estimate to use a property of the exact `Lambda`
weights that the staircase does not share, and state that property explicitly.
