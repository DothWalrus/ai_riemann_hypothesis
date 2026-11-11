# AI-assisted Riemann hypothesis research

A collaborative research log, collection of reproducible numerical checks,
and growing Lean formalization project centered on a probability-theoretic
reformulation of the Riemann hypothesis.

**This repository does not contain a proof or counterexample to the Riemann
hypothesis. No new zero-verification record or novel theorem is claimed.**

## The idea, without the technical background

The Riemann hypothesis predicts that certain zeros of the Riemann zeta function
all lie on one vertical line in the complex plane. These zeros are closely
connected with the distribution of prime numbers.

Our starting paper constructs a real function called `g`. The hypothesis is
equivalent to saying that `g` never rises above zero. Picture an endless
landscape: the goal is to prove that no hill anywhere rises above sea level.
Checking a finite stretch of that landscape is useful for testing our tools,
but it cannot establish the statement everywhere.

The starting point is Nakamura and Suzuki's 2023 paper,
[On infinitely divisible distributions related to the Riemann hypothesis](https://doi.org/10.1016/j.spl.2023.109889),
together with Suzuki's
[screw-function criteria](https://doi.org/10.1112/jlms.12785).

## What is currently here?

| Work | Status | What it does **not** establish |
| --- | --- | --- |
| Startup sign argument | Written argument and Python interval checks | A complete Lean proof for the actual function |
| Prime-side and zero-tail checks | Reproducible finite-range interval verification; together these cover `0 < t <= 40` | Global nonpositivity or a new zero-verification height |
| Finite Gram-matrix checks | Checks of explicitly specified matrices | Positivity for every matrix size and point set |
| GHS / Laplace analysis | Written derivation using established prior results | All higher-order inequalities needed for this approach |
| Second-order Laplace inequality and first Hankel determinant | Written argument with interval-checked constants, conditional on published zero verification; awaiting independent review | Anything about zeros above the verified height, or the higher-order inequalities |
| `RhCertificates.tangent_negative` | Lean-checked arithmetic implication | The analytic hypotheses connecting it to the screw function |

Here `t = 40` is an argument of the auxiliary function. It is **not** the height
of a zeta zero that has been newly checked.

Read [the progress report](docs/PROGRESS.md) for the evidence and limitations,
or [the research direction](docs/RESEARCH_DIRECTION.md) for the current proof gap.

## Run the Python checks

The core verification scripts use Python's standard library; they do not need
NumPy, SciPy, or a numerical zeta package. Use Python 3.11 or newer.

From the repository root:

```bash
python3 ns_startup_certificate.py
python3 -m unittest discover -s research -p 'test_*.py' -v
python3 research/screw_interval.py --limit 1000
python3 research/kernel_control.py
python3 research/zero_tail_certificate.py
python3 research/laplace_second_order.py
python3 research/laplace_numeric_crosscheck.py
```

The last command is an exploratory floating-point cross-check, not a
certificate; see [the second-order note](research/notes/laplace-second-order.txt).

The scripts assert the inequalities they check. A successful run ends without
an assertion failure. The zero-tail check uses a small embedded set of certified
zero enclosures and published external estimates; it does not calculate the
zeta function at enormous heights.

**Do not run the verification scripts with `python -O` or `PYTHONOPTIMIZE`.**
Their safety checks require assertions to remain enabled.

These are computer-assisted checks with explicit arithmetic bounds, not Lean
formalizations. Their mathematical reductions and external inputs still need
separate review.

Optional notebook tools can be installed into a virtual environment with
`python3 -m pip install -e '.[notebook]'`. These tools do not add an interactive
Lean kernel, and no such kernel is required for the checks above.

## Check the Lean result

The project pins Lean and Mathlib rather than requiring the latest release.
The explicit bootstrap command installs the missing tools and dependencies;
it reuses an existing `elan` installation when possible. Lake, Lean's project
manager, is included with the selected Lean toolchain.

From the repository root:

```bash
./formalization/bootstrap.sh
./formalization/lakew build
./formalization/lakew env lean RhCertificates/Tangent.lean
```

See [the Lean verification guide](docs/LEAN_VERIFICATION.md) for the exact setup,
version pins, certificate scope, and axiom reports.

The first setup downloads the matching toolchain, dependencies, and precompiled
Mathlib files. It can require several gigabytes of storage. Do not copy someone
else's downloaded toolchain into the repository.

The current theorem says that a particular linear expression is negative **if**
its intercept and slope satisfy specified bounds. Lean checks that implication.
It does not yet prove those bounds for the actual Nakamura–Suzuki function.

The repository also includes a [manual verification workflow](.github/workflows/verify.yml).
After publication, a maintainer can start it from GitHub's **Actions** tab. It
does not run automatically on pushes. No hosted run has been performed as part
of preparing these files. The workflow includes a check of the current Lean
theorem's axiom report; that check does not certify the broader analytic claims.

## Collaborate

This is a public repository: anyone may read it or propose a pull request.
Direct write access is granted by invitation. Proposed changes should be
reviewed before being merged; repository access and branch protection are
configured by the maintainers.

Contributions can improve explanations, independently audit an argument,
reproduce a check, formalize a lemma in Lean, or investigate one precise open
step. See [CONTRIBUTING.md](CONTRIBUTING.md).

Keep large toolchains, caches, credentials, personal session logs, and publisher
PDFs out of commits. Link to third-party papers and preserve the provenance and
licenses of external inputs.

## License and attribution

The project's original code and documentation are provided under the
[Apache License 2.0](LICENSE), unless a file states otherwise. This license does
not relicense third-party papers, datasets, or dependencies. Cite the original
mathematical sources and retain required notices when adapting their material.
