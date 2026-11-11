# Contributing

This project welcomes careful review, clear explanations, reproducible checks,
and small formalization steps. It does not claim to have solved the Riemann
hypothesis.

## Access and review

Anyone can read the public repository, open an issue where enabled, or propose
a pull request from a fork. Maintainers invite collaborators for direct write
access. Direct access does not make an argument correct: mathematical and code
changes should receive independent review before merging.

Use a separate branch for each focused change. Describe what changed, the
evidence supporting it, the commands you ran, and any remaining gap. Avoid
mixing a new research claim with unrelated cleanup.

## Describe the strength of every result

Use one of these descriptions in a report or pull request:

- **Lean-checked implication:** the exact theorem compiles, with all mathematical
  hypotheses visible. Explain whether those hypotheses have been established
  for the intended application.
- **Computer-assisted finite verification:** the stated bounded range is
  covered with justified numerical errors and mathematical reduction.
- **Written argument:** a derivation available for review, with sources and
  assumptions identified, but not fully formalized.
- **Exploratory computation or conjecture:** a useful test or proposed statement
  without a proof or rigorous certificate.

Do not present finite tests as a global theorem. Do not describe a numerical
residual, a successful Python run, or agreement between agents as a proof of RH.
Distinguish a new observation from a consequence or reproduction of prior work.

## Lean contributions

Keep the pinned `lean-toolchain` and `lake-manifest.json` unless a version update
is itself the purpose of the change. From the repository root:

```bash
./formalization/lakew build
./formalization/lakew env lean RhCertificates/Tangent.lean
```

For a new theorem, include its exact statement, the build output, an axiom
report, and a plain-language account of what has been proved. Do not add
`sorry`, `admit`, or a new mathematical axiom asserting the desired conclusion.

A theorem proved from an assumed bound is a valid implication, but it does not
certify that bound. Likewise, formalizing the final rational comparison from
a Python calculation does not formalize the entire analytic certificate.

Standard Lean logical foundations and external mathematical assumptions are
different things. Record both honestly; a standard axiom report is not a claim
that the compiler, dependency cache, or every imported library was independently
audited for this project.

## Python and numerical contributions

Run the checks listed in the README. Keep core scripts standard-library-only
unless a dependency is necessary and documented. Provide a small, bounded
reproduction rather than a long uncontrolled search.

Do not disable assertions using `python -O` or `PYTHONOPTIMIZE`; the verification
scripts use them to enforce their claimed inequalities.

For interval computations, explain rounding directions, truncation errors,
external input enclosures, and how the entire claimed domain is covered.
Sampling alone does not certify what happens between samples. Preserve an
independent check when a mathematical reduction or source constant changes.

Do not commit virtual environments, `.lake` builds, downloaded toolchains,
compiled caches, secrets, local account information, or unpublished private
communications. Add source URLs and provenance for data; include third-party
files only when redistribution is permitted by their licenses.

## Helpful first contributions

1. Reproduce the existing Python and Lean checks on another machine.
2. Improve the beginner explanations without strengthening the claims.
3. Audit the startup tangent/chord argument and its numerical hypotheses.
4. Formalize one analytic bridge required by that argument.
5. Investigate the next inequality described in
   [the research direction](docs/RESEARCH_DIRECTION.md), with a separate reviewer.

The repository's original contributions use Apache License 2.0 unless stated
otherwise. Preserve existing licenses and notices for adapted third-party work.
