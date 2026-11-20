# Lean verification

Lean checks formal proof terms against a precise theorem statement. A successful
build establishes that statement from its stated hypotheses and logical
foundations; it does not establish an unstated connection to the Riemann zeta
function.

## Current status

The main checked result is
[`StartupCertificate.lean`](../formalization/RhCertificates/StartupCertificate.lean).
It proves strict negativity of the explicitly defined smooth series for all
`t>0`, with the actual gamma/pi/log constant, and of its finite-sum extension
on `0<t<=log(2)`. The analytic, numerical, tangent and endpoint hypotheses are
proved rather than assumed in these final instances. Independent agents
reviewed the statements and replayed the sources.

**Status: kernel-checked for the explicit definitions.** Their identification
with the paper's special-function formula is now supplied by checked digamma,
Lerch-series and finite-sum bridges; the transcription was independently
reviewed. The global prime contribution and RH remain unresolved. See
[the exact statement and dependency report](../research/reports/2026-11-19-startup-certificate-synthesis.md).

### Original setup lemma

The original checked arithmetic implication is
`RhCertificates.tangent_negative`, in
[`formalization/RhCertificates/Tangent.lean`](../formalization/RhCertificates/Tangent.lean).

For real numbers `h`, `d`, and `t`, it proves:

```text
h < -1/40,  -1/32 < d < 0,  and  t >= 1/4
    imply h + d * (t - 1/2) < 0.
```

**Status: kernel-checked arithmetic; conditional with respect to its intended
analytic application.** The bounds on the actual screw function have not been
formalized by this arithmetic implication alone. The combined certificate above
now supplies the analytic and numerical components for the explicit series.
This original arithmetic implication alone does not prove the complete startup lemma, the Python
finite-range result, or RH.

The reported axioms are `propext`, `Classical.choice`, and `Quot.sound`, standard
logical foundations used by Mathlib. No `sorry` or `admit` holes or additional
mathematical axioms occur in this theorem. The recorded report is in
[`formalization/evidence/tangent-axioms.txt`](../formalization/evidence/tangent-axioms.txt).
Re-run the check rather than treating a saved log as a certificate by itself.

**Additional checked components, 2026-11-19:**

- [`Curvature.lean`](../formalization/RhCertificates/Curvature.lean) proves the
  exact curvature sign transition in `(1/4,1/3)`, with no Python input.
- [`SmoothSeries.lean`](../formalization/RhCertificates/SmoothSeries.lean) defines
  the displayed smooth series for an arbitrary real `C` and proves convergence,
  continuity at zero, its value zero there, individual summand derivatives and
  the exponential tail sum. `SmoothDerivatives.lean` supplies the separate
  proof of differentiation of the infinite sum on the positive half-line.

See the [detailed report](../research/reports/2026-11-19-curvature-series-agent.md)
for that checkpoint's scope and replay commands. Its analytic and numerical
obligations are now discharged by the combined certificate.
The saved logs disclose only the same three standard logical axioms. These
components feed the combined certificate above. They do not prove RH.

## Install and build

Prerequisites are Git, curl, and Python 3.11 or newer. On a fresh clone, run from
the repository root:

```sh
./formalization/bootstrap.sh
```

This explicit setup command reuses an existing elan installation when possible.
Otherwise it downloads the official installer into the project's `.tools`
directory and installs there without editing shell profiles. It then installs
the pinned compiler, materializes pinned dependencies, downloads the official
Mathlib cache, and builds/checks the theorem. Initial downloads require network
access and several gigabytes of disk space. It does not install an editor.

The ordinary build command does not install a missing compiler or automatically
fetch missing dependency sources/build caches:

```sh
./formalization/lakew build
./formalization/lakew env lean RhCertificates/StartupCertificate.lean
python3 scripts/verify_lean_certificates.py
```

The second command recompiles the main certificate and prints its axiom report.
The Python command builds registered project modules, recompiles every reachable
project source, and checks its explicitly printed axiom declarations. It writes
fresh `formalization/evidence/replay-*.txt` reports. Registration is through the
project imports in `formalization/RhCertificates.lean`; unregistered draft
sources are not silently treated as certificates. This tool does not replace
review of theorem statements or establish correspondence to unrelated prose.
To record
a new local report:

```sh
./formalization/lakew env lean RhCertificates/StartupCertificate.lean > startup-axioms.txt
```

`lakew` respects an explicitly configured `ELAN_HOME`, then checks a project-local
installation and a global elan installation. Other clients can also work from
`formalization/` using their ordinary `lake build`. The wrapper's dependency
preflight requires Python. Linux and macOS shell environments are supported;
Windows users can use a suitable shell or run the equivalent Lake commands.

## Pinned dependencies

- Lean: `leanprover/lean4:v4.35.0`.
- Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679` (release `v4.35.0`).
- Transitive revisions: [`formalization/lake-manifest.json`](../formalization/lake-manifest.json).

The toolchain, caches, and `.lake` build directories are intentionally excluded
from version control. Do not copy another contributor's installed toolchain
into the repository.

## Adding results

Each result must state its exact hypotheses and verification status:

1. **Kernel-checked:** successfully compiled with pinned dependencies, with no
   unfinished proofs or unproved mathematical assumptions hidden as axioms.
2. **Conditional kernel-checked:** a checked implication whose hypotheses are
   not yet established for the intended analytic objects.
3. **Draft/not checked:** source exists but has not successfully compiled.
4. **Not yet formalized:** only a written argument or external computation exists.

For computer-assisted proofs, formalize the bridge from numerical data to the
analytic claim, including rounding, truncation, and tail estimates. A Python
`PASS` message or a formalized last arithmetic comparison is not a Lean proof
of the entire result. Review `#print axioms` output for each main theorem.

The current setup uses the ordinary Lean/Mathlib trust model, including official
precompiled library artifacts. The compiler and all upstream proofs were not
independently re-audited or rebuilt as part of this project.
