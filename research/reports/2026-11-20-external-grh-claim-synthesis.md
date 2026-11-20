# External development: claimed Lean proof of GRH (reported 2026-11-20)

## In plain language

By 2026-11-20 (the date of the Scientific American report; the note itself is
undated), Levent Alpöge, a mathematician employed by Anthropic, publicly
announced that he believes he has proved the Generalized Riemann Hypothesis
(GRH), working with the AI model Claude. GRH is usually stated for Dirichlet
L-functions; the note does not specify the exact family, and it separately
mentions an "Extended" Riemann hypothesis as future work. Under any standard
formulation, GRH includes the ordinary Riemann hypothesis (RH) for the zeta
function as a special case. He has released the proof only as a Lean
formalization, together with a four-page informal note, and says a
human-readable version does not yet exist. The note states that the
formalization is finished and made without assumptions.

**This claim has not been checked by this project, and as of this report no
independent verification or refutation has been reported in the sources
below.** It is recorded here so that collaborators and their agents know
about it before spending more effort on the route this repository follows.

## Sources

- Announcement note: <https://alpo.ge/remark.pdf> (4 pages, informal; not a
  paper). Linked, not committed, following the repository's practice of
  linking external papers.
- Lean development, as cited in the note's footnote:
  `https://alpo.ge/lean.tar.gz.part01` through `part14`. **Not downloaded,
  built or inspected by this project.**
- News report: Scientific American, 2026-11-20,
  <https://www.scientificamerican.com/article/anthropic-mathematician-claims-to-prove-riemann-hypothesis-most-famous-problem-in-all-of-math/>.
  The article is marked as breaking news and may change. It quotes no expert
  assessment of correctness.

## What the note says about the method

The note is a personal account with a rough timeline of ingredients, not a
proof. The author says some technical descriptions paraphrase AI-written
summaries and may be revised. Read the summary below as a description of the
note, not as checked mathematics.

- **Model argument.** Stepanov's elementary method for the Riemann hypothesis
  for curves over finite fields (extended to all curves by Bombieri and
  Schmidt). The method uses an auxiliary function that vanishes to high
  multiplicity at the points being counted.
- **Central claimed idea.** Integers have no direct analogue of high-order
  vanishing. The note says this is replaced by a chain of iterated theta lifts
  between totally definite unitary groups, each lift contributing one unit of
  multiplicity. For a von Mangoldt sum of length `X` the chain length is
  taken to be about `sqrt(X)`.
- **Other named ingredients.**
  - The sign of a smoothed von Mangoldt sum from the Guinand–Weil explicit
    formula.
  - Determinant (Stepanov-type) constructions for automorphic periods
    (GGP/Bessel periods, seesaw, Rallis).
  - A relative trace formula.
  - Iwasawa towers, with a choice the note says uses Behrend.
  - The Bost slope inequality.
  - The Chowla–Selberg and Siegel mass formulas.
  - A weakening of Vandiver's conjecture for certain Galois cohomology classes.
    The note says this weakening was itself proved as part of the argument;
    Vandiver's conjecture is not assumed.
- **Size.** The note reports that an expanded written version ran to more than
  250,000 pages, which is why only the Lean source was released.

## Verification level

**None of the repository's four levels applies: nothing has been built or
reviewed here.** The repository's standard
([AGENTS.md](../../AGENTS.md), [LEAN_VERIFICATION.md](../../docs/LEAN_VERIFICATION.md))
would require checks 1–3 below before accepting a Lean claim. We add check 4
because of the weight of this claim.

1. Compile the exact development with its pinned dependencies.
2. Confirm that the final theorem states RH/GRH faithfully. For RH, for
   example, compare it with Mathlib's `RiemannHypothesis` definition if the
   development uses Mathlib.
3. Confirm there is no `sorry`, `admit` or added mathematical axiom, using an
   audited axiom report.
4. Rule out reliance on known Lean or toolchain soundness issues. (The
   repository otherwise uses the ordinary Lean/Mathlib trust model.)

None of these checks has been done here. Scientific American's reporter
expects experts to be able to check the Lean code quickly; no check has been
reported yet. Until a credible report appears, treat RH as **unproved** for the
purposes of this repository.

## Relation to this repository

- **Little overlap, as far as the note describes.** This repository studies
  the Nakamura–Suzuki function `g` and the criterion
  `RH <=> g(t) <= 0 for all real t`, together with finite certificates and
  complete-monotonicity hierarchies. The note never mentions `g` or that
  criterion, and its argument is mainly automorphic and arithmetic. There is
  one shared starting point. Like this repository (see
  [the Chebyshev-error note](../notes/chebyshev-error.txt)), it uses an
  RH-equivalent sign condition from the Guinand–Weil explicit formula for a
  weighted von Mangoldt sum, but proves it by a different route. Nothing in
  this repository is known to be an input to the argument. Whether the Lean
  development uses anything similar cannot be said without inspecting it.
- **If the claim is confirmed.** The global sign `g(t) <= 0` would follow
  immediately from the known equivalence, so this repository's research
  target would be settled as a corollary. The conditional note
  [quasi-rh-consequences](../notes/quasi-rh-consequences.txt) would be
  superseded, because RH implies its assumed zero-free half-plane
  `Re s > 7/8`. Existing finite results remain true, and the Lean startup
  certificate remains a valid formal result. A second proof by this route
  would still be mathematically legitimate, but it would no longer be the
  reason for the project.
- **If the claim fails.** Nothing changes. The open problem stays as recorded
  in [RESEARCH_DIRECTION.md](../../docs/RESEARCH_DIRECTION.md): uniform control
  of `g(t)` for unbounded `t`. The finite-verification approaches already
  shown to be blind to zeros above the verified height remain so.

## Recommendation (for the maintainer to decide)

1. **Pause new research spending on the global-sign route** until a credible
   independent check of the Lean development is reported. The outcome may be
   known soon, and work started now could be overtaken if the claim is
   confirmed.
2. **Do not let agents download or build the announced tarball automatically.**
   Building a Lean project can execute code, the source is external, and
   AGENTS.md does not authorize unscheduled spending. If the maintainer wants
   an in-house replay, do it deliberately, in an isolated environment, and
   record the results here using the four checks above.
3. **Revisit this report** when expert verification or refutation is
   published, and update [PROGRESS.md](../../docs/PROGRESS.md) and
   [RESEARCH_DIRECTION.md](../../docs/RESEARCH_DIRECTION.md) to match.

## Unresolved step

Whether the announced Lean development compiles, states RH/GRH faithfully and
depends only on standard axioms. This is outside the project's control and
should be decided by public expert review.

## Review

A Claude agent wrote this report at a collaborator's request, using the two
sources above. A separate agent then checked it against those sources and the
repository documents for misstatements, overclaims and broken links. Its 14
findings were applied. No mathematics in the announced proof was reviewed.
Both agents are Claude models made by Anthropic, the claimant's employer.
This is AI review, not maintainer review.
