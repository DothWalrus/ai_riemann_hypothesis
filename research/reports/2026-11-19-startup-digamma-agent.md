# Exact digamma-quarter normalization of the startup constant

## Plain-language outcome

The coefficient written in the source formula using the digamma value at 1/4
now has a kernel-checked identity with the gamma/pi/log constant used by the
explicit startup series. This closes one source-normalization boundary; it
does not identify the original Lerch term or the entire published function.
It is not an RH proof or a claim of mathematical novelty.

**Status: kernel-checked.** The five public declarations in
[StartupDigamma.lean](../../formalization/RhCertificates/StartupDigamma.lean)
compile without warnings and with only the standard logical axioms
`propext`, `Classical.choice`, and `Quot.sound`. No numerical enclosure or
special-value identity is introduced as a new axiom.

## Exact statements and complex/real distinction

Mathlib defines `Complex.digamma` as the logarithmic derivative of its complex
Gamma function. The theorem `digamma_quarter` proves

\[
\psi(1/4)=-\gamma-3\log 2-\frac\pi2
\]

as an equality in the complex numbers, with gamma, log(2) and pi explicitly
coerced from the reals. The lemma `digamma_quarter_im` separately proves its
imaginary part is zero; taking a real part therefore does not hide a leftover
imaginary contribution.

The theorem `complex_digamma_coefficient_eq_startupConstant` proves

\[
-\frac{\psi(1/4)-\log\pi}{2}=C
\]

in the complex numbers, where C is the real startupConstant coerced to Complex.
For an explicitly real coefficient, the file defines

    digammaLinearCoefficient = -Re(psi(1/4)-log(pi))/2

and proves `digammaLinearCoefficient_eq_startupConstant` in the reals.
The normalization is exactly the one used in the written startup note.

## Derivation inside the kernel

The proof instantiates Mathlib's digamma reflection and duplication formulas
at 1/4. Their side conditions are discharged internally: 1/4 is not an integer,
and 2*(1/4)=1/2 is not a nonpositive integer. The first fact follows from the
integer contradiction 4n=1; the second follows from nonnegativity of natural
numbers after taking real parts.

The cotangent factor is exactly one, using the already proved real value
tan(pi/4)=1 and its reciprocal, then the real-to-complex cotangent identity.
Thus reflection gives

    psi(3/4)=psi(1/4)+pi.

Duplication and Mathlib's proved half-value give

    psi(1/2)=(psi(1/4)+psi(3/4))/2+log(2),
    psi(1/2)=-2log(2)-gamma.

Substitution and ring arithmetic yield the quarter-value. The complex
logarithm at the positive real argument 2 is explicitly identified with the
real logarithm using the appropriate positive-real logarithm theorem. No
branch choice is silently discarded.

The pinned primary source inspected locally is
[Mathlib's digamma file](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/SpecialFunctions/Gamma/Digamma.lean),
which supplies the definitions, reflection formula, duplication formula and
half-value. The remaining work is exact algebra and coercion normalization.

## Replay and evidence

From the repository root:

```sh
./formalization/lakew env lean RhCertificates/StartupDigamma.lean
```

The final replay exited zero without warnings. See
[startup-digamma-build.txt](../../formalization/evidence/startup-digamma-build.txt)
for the exact replay command, pins and axiom listing. Development failures
were confined to explicit complex/real coercions; those failures are not
counted as successful proofs.

## Remaining step and next test

An independent agent must still review and replay this new module; the earlier
independent audits do not automatically cover this proof. It can then be
substituted into the existing explicit startup formula without retaining a
conditional assumption about its linear constant.

The next source-identity step is the Lerch expansion and the cancellation of
its k=0 term, or an explicit definition of that source term with a proved series
identity. Equality of constants alone is not equality of the whole published
g-function. Formal identification of the prime weights and the global
accumulated-prime cancellation problem remain separate obligations.
