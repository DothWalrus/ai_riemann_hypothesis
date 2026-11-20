# Research synthesis: checked startup formula and global method limits

## Main result

The startup formalization is complete for a transcription of Nakamura--Suzuki
(2023), equation (1.5). Lean proves `sourceFormula(t)<0` for
`0<t<=log(2)` and `sourceFormula(0)=0`. The actual digamma coefficient,
convergent Lerch defining series, von Mangoldt weights, finite cutoff,
series differentiation and exact numerical bounds are all included. Independent
agents reviewed the mathematical interpretation and replayed the exact sources.

See [the complete startup certificate report](2026-11-19-startup-certificate-synthesis.md)
and [StartupCertificate.lean](../../formalization/RhCertificates/StartupCertificate.lean).
This is a formalization of an established finite result. It proves neither the
global sign nor RH, and establishes no new zero-verification record.

## Global investigations

- [Artificial models](2026-11-19-global-prime-agent.md) and
  [supported staircases](2026-11-19-prime-support-agent.md) show why coarse
  normalization, monotonicity, support and PNT-shaped estimates do not determine
  the required one-sided sign. The abstract support/PNT assumptions and the
  distinction from actual arithmetic weights are explicit.
- [Arithmetic cancellation](2026-11-19-arithmetic-cancellation-agent.md)
  proves that the actual target weights at prime powers 2 and 4 violate a
  necessary inequality for exact nonnegative factorial-floor representations.
  The large-argument weight violation is kernel-checked; the general
  nonrepresentation conclusion follows from the checked necessary inequality.
- [Majorant loss](2026-11-19-majorant-loss-agent.md) proves a growing lower
  bound on the excess cost of nonnegative floor-kernel majorants, using the
  actual von Mangoldt weights and exact factorial reindexing. Its global
  barrier explicitly assumes a bounded permissible margin; no RH bridge is
  silently imported.
- [The signed factorial attempt](2026-11-19-signed-factorial-attempt-agent.md)
  fails to produce a better global bound. Its finite Abel identity, actual
  Stirling remainder steps and related finite lemmas are checked in Lean.
  The full Möbius inversion and coarse `O(sqrt(x))` estimate are written
  derivations rather than complete Lean certificates. Their scope was
  independently reviewed.

These findings limit specific proposed deductions. They do not establish the
needed one-sided cancellation for actual primes, and no novelty is claimed.

## Verification status

All cited Lean modules compiled individually with the pinned Lean/Mathlib
dependencies, and their exact statements received independent review/replay.
The printed axiom reports contain only `propext`, `Classical.choice` and
`Quot.sound`. The final source-formula theorem has no unproved analytic or
numerical premise and uses no Python result as an axiom.

The final aggregate build and source replay were completed successfully during
subsequent daily sync validation: **160 declarations across 17 registered
modules** were rebuilt and their printed axiom reports audited. All **36 Python
unit tests** passed (29 research tests and seven axiom-checker tests), and the
arithmetic floor diagnostic passed. The previously pending integration check
is now complete. See [the verification summary](../../formalization/evidence/sync-verification-summary.txt).
Reproduce the checks from the repository root:

```sh
python3 scripts/verify_lean_certificates.py
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 -m unittest discover -s research -p 'test_*.py' -v
```

The replay command builds the registered modules, recompiles their source and
audits every explicit printed declaration. The manual GitHub workflow now uses
the same replay command. No hosted workflow was started while preparing this
work. Saved logs and agent agreement do not replace replay or statement review.

## Exact unresolved step and next test

The global mathematical gap remains a one-sided cancellation estimate for the
actual weighted Chebyshev error `J(x)` at unbounded `x`. The signed approach
still contains uncontrolled Möbius-weighted sums; merely rewriting them or
assuming subpower cancellation would not be a proof.

The aggregate replay is complete. The next formalization target is the
finite zero-tail checker's correctness theorem with all external zero and
counting assumptions explicit. The next global proof attempt must identify an
arithmetic property beyond the coarse information excluded by the models and
derive a justified one-sided estimate from it. See
[the current research direction](../../docs/RESEARCH_DIRECTION.md).
