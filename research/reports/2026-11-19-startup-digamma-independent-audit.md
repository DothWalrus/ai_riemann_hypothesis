# Independent audit of the digamma coefficient bridge

## Outcome and exact statements

The exact [StartupDigamma.lean](../../formalization/RhCertificates/StartupDigamma.lean)
source passed independent mathematical review and source replay. Its SHA256 is
`47d93d48b6de955aa5738dbfbed1912948e292373be780eb6bd4b21890fe2e91`.
All five printed declarations compiled with only the standard three logical
axioms.

**Verification level: kernel-checked.** The source proves the complex identity

\[
\psi(1/4)=-\gamma-3\log2-\pi/2,
\]

and hence

\[
-\frac{\psi(1/4)-\log\pi}{2}
=\frac{\gamma+\pi/2+3\log2+\log\pi}{2}=C.
\]

The complex equality explicitly casts the real constant into the complex
numbers. A separate theorem identifies its real projection with the defined
`startupConstant`, and another proves the imaginary part of `psi(1/4)` is zero.
This closes the linear-coefficient identification; it does not by itself
identify the Lerch term or establish the global sign of the full screw function.
No novelty or RH proof is claimed.

## Independent mathematical checks

1. **Reflection side condition.** `1/4` is not an integer. The source checks
   this for every integer by taking real parts, clearing the denominator, and
   deriving the impossible integer equation `4*n=1`. Thus Mathlib's digamma
   reflection formula is used away from all its excluded integer points.
2. **Duplication side condition.** `2*(1/4)=1/2` cannot be the negative of a
   natural number. The real projection and nonnegativity of that natural cast
   discharge the exact pole condition in the pinned duplication theorem.
3. **Cotangent.** The real identity `tan(pi/4)=1` gives `cot(pi/4)=1` by
   inversion. Mathlib's real-to-complex cotangent identity transfers it to the
   exact complex argument used in the reflection formula.
4. **Complex logarithm.** The identity `Complex.log(2)=ofReal(log(2))` is
   applied at a positive real argument. There is no unproved branch choice or
   omitted imaginary multiple of pi.
5. **Signs and factors.** Reflection gives
   `psi(3/4)=psi(1/4)+pi`; duplication gives
   `psi(1/2)=(psi(1/4)+psi(3/4))/2+log(2)`. Substituting the proved half-value
   `psi(1/2)=-gamma-2*log(2)` yields the quarter-value with **minus pi/2**.
   The subsequent negative outer half factor yields **plus pi/4** in `C`.
6. **Real identification.** The closed form consists entirely of real casts,
   so its imaginary part is proved zero. The real coefficient equality is
   checked by explicit projection and algebra, rather than treating a complex
   expression as a real number without justification.

The inspected primary source for reflection and duplication was the pinned
local Mathlib file `Mathlib/Analysis/SpecialFunctions/Gamma/Digamma.lean`.
The proof depends on its established gamma/digamma identities, not on numerical
digamma evaluation or an added special-value axiom.

## Independent replay and axiom audit

```sh
./formalization/lakew env lean RhCertificates/StartupDigamma.lean
```

Exit status was zero with no warnings. Every listed declaration has exactly
`propext`, `Classical.choice`, and `Quot.sound` in its dependency report. No
`sorryAx`, new mathematical axiom or native-computation axiom occurs. Evidence:
[startup-digamma-independent-replay.txt](../../formalization/evidence/startup-digamma-independent-replay.txt).

Lean remains pinned to `leanprover/lean4:v4.35.0` and Mathlib to
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

## Remaining step and next test

The remaining startup identification task is the Lerch-series reduction and its
combination with the finite prime contribution for the original displayed
formula. The exact coefficient is now accounted for. Even after that startup
identification, control of the accumulated prime contribution for unbounded
arguments remains the global RH-strength gap.
