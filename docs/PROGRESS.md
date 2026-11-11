# Progress and verification status

Status as of 2026-11-11: **no proof or counterexample to the Riemann hypothesis;
no new zero-verification record; no claim of a novel theorem.**

## The research target

Nakamura–Suzuki define an even real function `g` whose exponential is an
infinitely divisible characteristic function exactly when RH holds. Suzuki's
related pointwise criterion says that RH is equivalent to `g(t) <= 0` for every
real `t`. This equivalence is established prior work, not a result of this
repository.

In less technical language, we are trying to prove that an explicitly defined
landscape never rises above zero. Our bounded checks verify tools for examining
parts of that landscape; a proof must still cover the whole infinite domain.

## What has been checked?

### Startup argument and prime-side intervals

The written startup argument establishes strict negativity for
`0 < t <= log(2)` using the smooth part's curvature, a tangent bound, and a convex
chord. Its Python companion encloses the constants and elementary-function
errors using directed Decimal arithmetic.

The prime-side checker treats each interval between consecutive prime-power
events separately. A run through `log(1000)` covers 194 intervals. These are
continuous interval bounds, not a grid of isolated samples.

Small-interval positivity is already discussed in Suzuki's 2023 paper. This
work supplies reproducible controls and does not claim a new local theorem.
The complete startup argument is in [ns_startup_lemma.md](../ns_startup_lemma.md).

### Finite zero-tail certificate

The zero-tail script verifies `g(t) < 0` throughout `1/2 <= t <= 40` using:

- enclosures of five positive zero ordinates from LMFDB;
- Platt–Trudgian's established verification of critical-line zeros through
  height `3 * 10^12`;
- Bellotti–Wong's explicit bound for the number of zeros at higher heights;
- outward arithmetic, a cosine remainder bound, and continuous Lipschitz-cell
  coverage.

The checked run accepts 743 cells. Together with the startup argument it covers
`0 < t <= 40`. The source assumptions and mathematical reduction matter: the
script is not a standalone formal proof of those published external results.

The parameter `t` is the argument of `g`. This statement does not increase the
height to which RH itself has been verified. No amount of repeating this finite
test settles the unbounded tail.
The detailed derivation and external input bounds are in
[the zero-tail proof note](../research/notes/zero-tail.txt).

### Finite kernel tests

An interval LDL calculation verifies the specified eight-by-eight anchored
kernel matrix at `t = 1/2, 1, ..., 4`, including its 28 two-by-two principal
minors. This checks an explicit finite object; it does not prove positivity for
all point sets, all matrix sizes, or the associated infinite-dimensional
operator.

### Analytic first-order inequality

For

\[
\kappa(w)=\log\frac{\xi(1/2+w)}{\xi(1/2)},\qquad
L(w)=\frac{\kappa'(w)}{w^2},\qquad w>0,
\]

the notes explain how Newman's established theta-kernel result and a one-site
GHS argument give

\[
\kappa'''(w)\le0,\qquad
w\kappa''(w)\le\kappa'(w),\qquad L(w)>0,\quad L'(w)<0.
\]

This is a derivation from prior theory. It has not been fully formalized in
Lean here, and first-order monotonicity is insufficient for the proposed global
proof route. The xi-specific potential property is supplied by Newman's
published theorem; this project does not reprove that entire theorem.

## What does Lean currently certify?

`RhCertificates.tangent_negative` checks this arithmetic implication:

If real numbers `h`, `d`, and `t` satisfy

\[
h<-1/40,\quad -1/32<d<0,\quad t\ge1/4,
\]

then

\[
h+d(t-1/2)<0.
\]

The theorem compiles without unfinished proofs or added mathematical axioms.
Its axiom report lists `propext`, `Classical.choice`, and `Quot.sound`, the
standard logical foundations used in this Mathlib proof.

It does **not** certify that the actual screw function has the assumed
intercept or slope, nor that its analytic tangent and chord arguments apply.
Consequently the full startup result and finite zero-tail certificate are
**not yet Lean-certified**.

## The remaining gap

The global sign of `g` remains unproved. The current analytic route needs
higher-order inequalities for `L`, or corresponding transformed moment-matrix
positivity. GHS provides an upper bound on a third derivative, whereas the next
conditions need a quantitative lower bound. See
[RESEARCH_DIRECTION.md](RESEARCH_DIRECTION.md).

## Primary references

- Nakamura and Suzuki (2023),
  [On infinitely divisible distributions related to the Riemann hypothesis](https://doi.org/10.1016/j.spl.2023.109889).
- Suzuki (2023),
  [Aspects of the screw function corresponding to the Riemann zeta-function](https://doi.org/10.1112/jlms.12785).
- Newman (1991),
  [The GHS inequality and the Riemann hypothesis](https://doi.org/10.1007/BF01888165).
- [Platt–Trudgian's rigorous zero verification](https://arxiv.org/abs/2004.09765).
- [Bellotti–Wong, version 2, Theorem 1.1](https://arxiv.org/html/2412.15470v2).
- [LMFDB's zero-data provenance](https://www.lmfdb.org/zeros/zeta/Source).

These links identify external work. The repository's license does not relicense
the linked papers or their data.
