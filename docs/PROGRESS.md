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

### Second-order inequality and first Hankel determinant

Status: **written argument with interval-checked constants; not yet
independently reviewed; not formalized in Lean; no novelty claimed.**

[The second-order note](../research/notes/laplace-second-order.txt) argues that,
given Platt–Trudgian's zero verification, the Bellotti–Wong counting bound,
and the location of the first zero,

\[
L''(w)>0,\qquad L(w)L''(w)-[L'(w)]^2>0\qquad\text{for every } w>0 .
\]

These are the two lower bounds on `c_3` that the research direction named as
the next target. For `0 < w <= 20` the zero expansion of `L` is used: verified
zeros contribute with the right sign and the unverified tail is smaller by a
factor of more than `10^5`. For `w >= 20` the explicit formula with elementary
digamma and prime-sum bounds is used. The same zero-side estimate gives every
derivative sign `(-1)^n L^{(n)} > 0` on `0 < w <= 10^5`.

`research/laplace_second_order.py` checks the constants with outward-rounded
intervals. `research/laplace_numeric_crosscheck.py` is a separate exploratory
floating-point comparison that uses the theta kernel and no zero data.

**This result does not bring the programme closer to RH.** The argument never
examines zeros above height `3 * 10^12`, so these inequalities would hold
whether or not RH fails there. It shows that a fixed finite number of the
required inequalities follows from finite verification; the open problem is
a statement uniform in the derivative order.

### What the Laplace hierarchy measures

Status: **written arguments with one independent AI re-derivation, awaiting
maintainer review; the order estimate is heuristic; the toy-model computation
is exploratory; no novelty claimed.**

[The map note](../research/notes/post-widder-map.txt) records three facts about
the normalized derivatives `c_n(w) = (-1)^n w^(n+1) L^(n)(w)/n!`:

1. For `w > 1/2`, `c_n(w)` is a Gamma-window average of `-g` (Post–Widder),
   so complete monotonicity of `L` is the pointwise sign of `g` at finite
   resolution.
2. Given the external inputs of the second-order note, `c_n(w) > 0` whenever
   `w <= 9 * 10^24` and `n + 1 > 1.184 * 10^-11 w^2`. These inequalities hold
   whatever the zeros above the verified height do.
3. Unconditionally, an off-line zero `1/2 + b + ia` forces infinitely many
   negative `c_n(w)` at every `w > (a^2+b^2)/(2b)`; below the least such
   threshold `c_n(w)` tends to a positive constant. RH is therefore
   equivalent to eventual sign-regularity at an unbounded set of `w`.

`research/postwidder_toy.py` illustrates item 3 on an artificial function
with one invented off-line zero. It makes no statement about zeta.

These results explain why the route is hard; they do not advance it.

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
every higher-order inequality for `L`, or the corresponding transformed
moment-matrix positivity for every size. The second-order note indicates that
any single fixed order is likely reachable from finite zero verification and
therefore uninformative; the missing ingredient is control that is uniform in
the order. See [RESEARCH_DIRECTION.md](RESEARCH_DIRECTION.md).

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
