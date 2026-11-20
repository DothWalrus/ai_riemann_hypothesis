# Independent startup audit

**Status:** independent mathematical review and Python replay completed for the
existing startup note. The new Lean files have since been independently
recompiled and reviewed in the linked follow-up report. This is not an RH proof or a full Lean certificate for the actual
Nakamura--Suzuki function.

The audit independently checked the source paper's formula (1.5) visually on
page 2 against ns_startup_lemma.md. The k=0 cancellation, locally uniform
first- and second-derivative series, formula for H'', cubic sign transition,
first-derivative expression, supporting tangent and initial chord all agree.
No mathematical error in the finite startup sign argument was found.

H is continuous at zero because the summands are uniformly bounded by a
summable inverse-square sequence. H' diverges to negative infinity there;
closed-interval convexity must use continuity plus interior curvature, not a
finite derivative at zero. This is a real formalization obligation, not a
counterexample to the argument.

The existing Python startup certificate and four certificate safety tests
passed. Its directed arithmetic, alternating arctangent remainder, positive
arctanh tail, truncation direction and Euler--Maclaurin remainder sign were
checked independently. Python's transcendental implementation guarantees and
the analytic remainder theorem remain outside the Lean kernel.

The exact generic StartupGeometry.lean statement/proof was independently
reviewed mathematically: its closed-interval convexity, tail concavity,
full HasDerivAt at 1/2, zero value, and rational inequalities are explicit
hypotheses, with no circular assumed negativity. The a<=1/2 boundary is valid
because full differentiability at the tangent point is assumed. The owner
reports successful compilation with the standard three logical axioms;
this checkpoint has not independently replayed that compilation.

One wording caveat: positive prime-power derivative jumps defeat the global
concavity justification, but positivity alone does not logically disprove every
possible global tangent inequality. This does not affect the startup proof.

The first unresolved step is proving the hypotheses for the actual H in Lean,
including series convergence/differentiation and numerical bounds. The next
test is to independently review the new Curvature.lean and SmoothSeries.lean
and their evidence. PrimeObstruction.lean and the artificial staircase model
also remain under independent review; no conclusion about actual Chebyshev
weights or RH follows from artificial non-arithmetic countermodels.

Replay commands used from the repository root:

    PYTHONDONTWRITEBYTECODE=1 python3 ns_startup_certificate.py
    PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s research -p 'test_certificate_safety.py' -v

Both passed. A Python PASS does not certify the analytic-to-Lean bridge.

## Completed independent follow-up

The exact generic geometry theorem and its derivative wrappers, Curvature.lean,
and the 15-declaration SmoothSeries.lean checkpoint were independently
recompiled successfully, with only propext, Classical.choice and Quot.sound.
The detailed completed review and exact remaining analytic bridge appear in
[the independent follow-up audit](2026-11-19-independent-research-audit.md).
The earlier checkpoint statements about pending replay are superseded by that
review. No full Lean certificate of the actual startup function or RH is claimed.

## Independent prime-cutoff replay

PrimeStartup.lean was independently reviewed and replayed successfully after
its final cleanup. Its four printed declarations use only the standard three
logical axioms. For every n in the finite interval from 2 to floor(exp t),
positivity and the floor bound imply log(n)<=t, while n>=2 implies
log(2)<=log(n). Under t<=log(2), each factor t-log(n) is exactly zero.
Thus the endpoint n=2 is correctly retained and annihilated, rather than
incorrectly removed. The result needs no sign assumption on the arbitrary
weights. The transfer theorem explicitly assumes the separate smooth-part
negativity result; it does not assert that result without proof.

Independent command: `./formalization/lakew env lean RhCertificates/PrimeStartup.lean`.
The formula and its Nat.floor cutoff match the stated finite expression.
Identifying the arbitrary weights with Lambda(n)/sqrt(n), treating Lambda(1)=0,
and identifying the smooth series with the original special-function formula
remain explicit representation steps. Nothing beyond the first prime event
is controlled by this vanishing proof.
