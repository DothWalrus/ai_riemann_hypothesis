# Lean verification

Lean checks formal proof terms against a precise theorem statement. A successful
build establishes that statement from its stated hypotheses and logical
foundations; it does not establish an unstated connection to the Riemann zeta
function.

## Current status

The repository contains one checked arithmetic implication:
`RhCertificates.tangent_negative`, in
[`formalization/RhCertificates/Tangent.lean`](../formalization/RhCertificates/Tangent.lean).

For real numbers `h`, `d`, and `t`, it proves:

```text
h < -1/40,  -1/32 < d < 0,  and  t >= 1/4
    imply h + d * (t - 1/2) < 0.
```

**Status: kernel-checked arithmetic; conditional with respect to its intended
analytic application.** The bounds on the actual screw function, the supporting
tangent inequality, and the convex-chord argument have not been formalized.
This certificate does not prove the complete startup lemma, the Python
finite-range result, or RH.

The reported axioms are `propext`, `Classical.choice`, and `Quot.sound`, standard
logical foundations used by Mathlib. No `sorry` or `admit` holes or additional
mathematical axioms occur in this theorem. The recorded report is in
[`formalization/evidence/tangent-axioms.txt`](../formalization/evidence/tangent-axioms.txt).
Re-run the check rather than treating a saved log as a certificate by itself.

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
./formalization/lakew env lean RhCertificates/Tangent.lean
```

The second command recompiles the source and prints its axiom report. To record
a new local report:

```sh
./formalization/lakew env lean RhCertificates/Tangent.lean > tangent-axioms.txt
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
