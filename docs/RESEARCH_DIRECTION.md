# Current research direction

This document records a precise next question, not a proposed proof of RH.
It supplements the beginner overview in the [README](../README.md) and the
[verification-status report](PROGRESS.md).

## Start with the correct global question

Let `g` be the real even function in equation (1.5) of Nakamura–Suzuki's
[2023 paper](https://doi.org/10.1016/j.spl.2023.109889). The required global sign
is `g(t) <= 0` for all real `t`. The equivalent criterion is prior art.

There are two connected routes worth investigating:

1. Prove the global sign directly from the prime-side formula, controlling the
   contribution accumulated at prime powers.
2. Prove the positivity of transformed moment matrices, or complete
   monotonicity of an associated Laplace transform, using structure specific to
   the Riemann xi-function.

Merely deriving another RH-equivalent condition does not establish it.

## A precise next analytic inequality

For real `w > 0`, define

\[
\kappa(w)=\log\frac{\xi(1/2+w)}{\xi(1/2)},\qquad
\mu=\kappa'(w),\quad v=\kappa''(w),\quad c_3=\kappa'''(w),\qquad
L(w)=\frac{\mu}{w^2}.
\]

The current notes justify `mu > 0`, `v > 0`, and, using established
theta-kernel/GHS theory, `c_3 <= 0` and `w*v <= mu`. This gives `L > 0` and
`L' < 0`.

The next derivative sign would require

\[
L''(w)\ge0
\quad\Longleftrightarrow\quad
w^2c_3\ge4wv-6\mu.
\]

The first ordinary transformed Hankel determinant is

\[
L(w)L''(w)-[L'(w)]^2
=\frac{2\mu^2+w^2(\mu c_3-v^2)}{w^6}.
\]

Its nonnegativity therefore requires the lower bound

\[
c_3\ge\frac{v^2}{\mu}-\frac{2\mu}{w^2}.
\]

GHS gives an upper bound on `c_3`, not this lower bound.

**Update, 2026-11-11.** [The second-order note](../research/notes/laplace-second-order.txt)
gives a written argument, awaiting independent review, for both lower bounds
on all of `w > 0`. It does not use the theta kernel. It uses published zero
verification for small `w` and the explicit formula for large `w`. That is
also its weakness: the argument is blind to zeros above the verified height,
so these two inequalities turn out to carry no information about RH beyond
the verification itself. Treat them as settled bookkeeping pending review,
not as partial progress toward the hierarchy.

## The question that replaces it

The same note shows every derivative sign `(-1)^n L^{(n)}(w) > 0` on the
bounded range `0 < w <= 10^5`, while each fixed order is known to hold for
`w` beyond a threshold that grows roughly linearly with `n`. A fixed order can
therefore be expected to follow by patching the two regimes. The unresolved
content of this route is uniformity in `n`:

- For which pairs `(n, w)` does neither the verified zeros nor the explicit
  formula decide the sign of `(-1)^n L^{(n)}(w)`? High orders at the point `w`
  are sensitive to primes once `n` is comparable to `w log 2`.
- Is there any inequality in the hierarchy whose proof would be forced to use
  zeros above the verified height? An approach that cannot name one is
  reproducing finite verification.

A useful contribution addresses one of these, or reviews the second-order
note. Proving one more fixed order by the same patching is not useful.

## Approaches already known to be insufficient

- **Positive weights alone.** Some prime-side terms push `g` upward. Assigning
  positive real-zero spectral weights before proving real-zero support assumes
  the desired conclusion.
- **Generic GHS or strong logconcavity.** These properties do not imply complete
  monotonicity. A Gaussian-smoothed three-point distribution supplies a test
  example with those properties but a moment-generating function having zeros
  in the right half-plane.
- **A fixed finite zero prefix.** Its phase contributions return arbitrarily
  close to zero, while the available bound for the unknown tail grows with
  `t`. The finite certificate cannot be promoted to a uniform global bound.
- **Continued Mellin values as ordinary integrals.** A meromorphically continued
  value does not justify cancellation by a convergent improper integral. The
  relevant signed moment fails to converge.
- **Finite matrices or sampling grids.** Their positivity does not establish
  the all-points or all-orders statement.

## Formalization sequence

The first Lean target is deliberately smaller than the research question:

1. Keep the already checked arithmetic tangent implication reproducible.
2. Formalize the analytic tangent/chord lemma with explicit hypotheses.
3. Prove those hypotheses for the actual smooth part of `g`.
4. Connect exact numerical enclosures to the analytic estimates.
5. Only then describe the startup sign result as fully Lean-certified.

The finite zero-tail certificate additionally depends on published zero
verification and explicit counting estimates. Those dependencies must be
formalized, imported as existing formal results, or explicitly retained as
hypotheses. A last-step arithmetic proof alone does not certify the whole chain.

## A useful research report

For each bounded attempt, record the exact statement, sources, assumptions,
derivation or code, independent review, first unresolved step, and one concrete
next test. Clearly distinguish a checked result from a conjecture or a restated
equivalence. Do not include private account, machine, or scheduling details in
public reports.
