# Independent audit of the startup constant bounds

## Result

The exact source [StartupConstants.lean](../../formalization/RhCertificates/StartupConstants.lean)
was reviewed independently of its author and replayed successfully. The theorem
`RhCertificates.startupConstant_bounds` proves

\[
\frac{67}{25}<C<\frac{2691}{1000},\qquad
C=\frac{\gamma+\pi/2+3\log2+\log\pi}{2}.
\]

**Verification level: kernel-checked for this exact real constant.** No novelty
is claimed. The statement by itself is a constant bound, not the full startup
sign result or a proof of RH.

## Mathematical checks

- The definition matches the written startup coefficient
  `gamma/2+pi/4+3*log(2)/2+log(pi)/2`; there is no missing factor of two.
- Mathlib's lower Euler--Mascheroni sequence at index63 uses `H_63-log(64)`;
  its upper sequence at64 uses `H_64-log(64)`. The selected indices therefore
  have matching logarithms. Exact rational harmonic bounds and Mathlib's
  logarithm bounds yield `569/1000<gamma<293/500`.
- The logarithm-series parameters `107/207` and `1071/2071` are exactly
  `(x-1)/(x+1)` for `x=157/50` and `x=1571/500`, respectively. The bounds
  transfer in the correct direction using strict monotonicity of log and
  Mathlib's proved pi bounds. They yield `143/125<log(pi)<229/200`.
- Combining those inequalities with the proved `log(2)` and pi bounds by
  linear arithmetic gives the stated coarse enclosure for `C`.

All arithmetic is internal to Lean's proof terms. No Python output or unproved
decimal enclosure is introduced. The proof invokes established Mathlib
theorems, whose logical dependency report is included below.

## Independent replay

```sh
./formalization/lakew env lean RhCertificates/StartupConstants.lean
```

Exit status was zero. All five printed declarations depend exactly on
`propext`, `Classical.choice`, and `Quot.sound`; there is no `sorryAx` or added
mathematical axiom. See
[startup-constants-independent-replay.txt](../../formalization/evidence/startup-constants-independent-replay.txt).
The project pins Lean `leanprover/lean4:v4.35.0` and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

The next obligation is to use this enclosure in exact value and slope bounds
for the defined smooth series and then apply the compiled startup geometry.
