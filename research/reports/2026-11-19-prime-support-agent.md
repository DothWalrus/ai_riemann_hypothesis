# Supported event staircases: a conditional Lean countermodel

This extends the [first obstruction report](2026-11-19-global-prime-agent.md).
The result concerns artificial event weights, not the actual von Mangoldt
weights. It does not prove or disprove RH, certify a new zeta-zero range, or
claim mathematical novelty.

**Plain-language outcome:** even keeping the locations and positivity of
counting-function jumps does not make a prime-number-theorem error estimate
determine the needed sign. The exact weights still matter. The new Lean file
constructs an abstract staircase and verifies this obstruction under explicit
support and asymptotic hypotheses.

## Exact construction and assumptions

Let `q : Nat -> Real` be strictly increasing, unbounded above, and `q(0)>1`.
Define

\[
N_q(x)=\min\{n:x<q_n\},\qquad Q_q(x)=q_{N_q(x)},
\]

and the artificial staircase

\[
\Psi_q(x)=\begin{cases}
0,&x<q_0,\\
Q_q(x)+q_0,&x\ge q_0.
\end{cases}
\]

Unboundedness ensures `N_q` exists. Strict increase and unboundedness imply
there are only finitely many event indices below any finite upper bound.
For `q_n <= x < q_(n+1)`, the next-event index is exactly `n+1`, hence
`Psi_q(x)=q_(n+1)+q_0`. Those intervals cover `[q_0,infinity)`.

Thus `Psi_q(1)=0`; it is nonnegative, nondecreasing, and right-continuous.
Its only possible jumps are at the specified events. Its first jump is
`q_1+q_0`; later jumps are `q_(n+1)-q_n>0`.

To obtain the asymptotic estimates, additionally assume a real-valued function
`count` and positive constants `C,c` with an onset `X` such that:

1. For every `x <= y < Q_q(x)`, `count(y)=count(x)`. This is the exact
   no-event/no-jump support premise used by the proof.
2. For every `y >= X`,

\[
|\operatorname{count}(y)-y|\le C D_c(y),
\qquad D_c(y)=y e^{-c\sqrt{\log y}}.
\tag{P}
\]

These are **external hypotheses**, not newly asserted zeta facts. The Lean file
does not instantiate `q` as the genuine prime powers or `count` as Chebyshev's
function, and does not import or prove a classical PNT error theorem.

Under these assumptions it proves, eventually as `x` grows,

\[
0<Q_q(x)-x\le4C D_c(x),\qquad
|\Psi_q(x)-x|\le4C D_c(x)+q_0,\qquad
\frac{\Psi_q(x)}x\longrightarrow1.
\]

The fixed additive `q_0` is retained explicitly in the formal error bound.

## The weighted error is eventually positive

Use the project kernel in logarithmic coordinates:

\[
J_q(t)=\int_0^t
 \bigl(\Psi_q(e^v)-e^v\bigr)e^{-v/2}
 \left(1+\tfrac12(t-v)\right)\,dv.
\]

Put `a=log(q_0)`. Before `a`, the staircase is nonnegative, and after `a`,
`Psi_q(exp(v))-exp(v) >= q_0=exp(a)`. The first batch's integral-comparison
lemma therefore gives

\[
J_q(t)\ge t+4-4e^{a/2}\qquad(t\ge a).
\]

In particular,

\[
J_q(t)>0\quad\text{if}\quad
t\ge\max\{a,4e^{a/2}\}.
\]

This time Lean also proves the staircase's weighted integrability from its
monotonicity and the continuity of the other factors. No integrability or
desired sign is silently assumed in the combined countermodel theorem.

For the written prime-power example `q_0=2`, this recovers
`J_q(t) >= t+4-4 sqrt(2)`. The exact substitution between the original
`u`-integral and these logarithmic coordinates remains a standard written
change of variables; the displayed logarithmic integral is the one Lean checks.

## No-jump argument, including endpoint conditions

Here is the precise derivation of the factor 4 in the gap estimate. Choose `x`
large enough that

\[
x\ge1,\quad x\ge X,\quad
4C e^{-c\sqrt{\log x}}\le1.
\]

Let `r=D_c(x)>0`, `h=4Cr`, and `y=x+h`. The last condition implies
`x <= y <= 2x`. Monotonicity of `log` and `sqrt`, followed by exponential
monotonicity, gives

\[
D_c(y)\le2D_c(x)=2r.
\]

Both endpoints lie beyond `X`, so (P) gives

\[
\operatorname{count}(y)\ge y-2Cr,\qquad
\operatorname{count}(x)\le x+Cr,
\]

and consequently

\[
\operatorname{count}(y)-\operatorname{count}(x)
\ge h-3Cr=Cr>0.
\]

If `y<Q_q(x)`, the support premise says the two values are equal, which is
a contradiction. Hence `Q_q(x)<=y` and `Q_q(x)-x<=h`.

The conclusion deliberately permits `Q_q(x)=y`: an event exactly at the
right endpoint is allowed. The no-jump premise is used only for strict
`y<Q_q(x)`, so the proof does not lose a boundary event. The left endpoint
`x` is included in `count(x)`, and no jump after `x` is available until
`Q_q(x)`, matching the usual right-continuous counting convention.

Since `c>0`, `exp(-c sqrt(log x)) -> 0`; the smallness condition is eventually
automatic. Lean proves that limit, derives the eventual gap estimate, and
squeezes `(Q_q(x)-x)/x` to zero. Adding `q_0/x -> 0` gives the staircase ratio.

## Lean statements and replay

Status: **conditional kernel-checked**, with the abstract event sequence,
no-jump support premise, and PNT envelope explicitly quantified.

Source: [PrimeSupport.lean](../../formalization/RhCertificates/PrimeSupport.lean).
Evidence: [prime-support-build.txt](../../formalization/evidence/prime-support-build.txt).
The source leaves the already audited `PrimeObstruction.lean` unchanged.

Important checked declarations include:

| Declaration | Exact role |
| --- | --- |
| `event_indices_below_finite`, `event_gaps_cover` | Local finiteness and coverage by successive event gaps |
| `staircase_on_event_gap` | Actual next-event staircase construction and its constant values between events |
| `staircase_normalized`, `staircase_monotone`, `staircase_positive_event_increment` | Normalization, monotonicity, and positive event increments |
| `staircase_right_continuous` | Right continuity, proved from a right-sided constant interval at every point |
| `staircaseLog_weighted_integrable` | Integrability of the weighted error of the constructed function |
| `staircase_weighted_lower`, `staircase_weighted_eventually_pos` | Full integral comparison and eventual positive sign |
| `nextEvent_gap_of_pnt_envelope` | Pointwise gap estimate with every large-`x` condition explicit |
| `nextEvent_eventual_gap_of_pnt_envelope` | Eventual gap estimate from a supported counting function with (P) |
| `staircase_ratio_of_pnt_count_envelope` | PNT ratio derived from those same hypotheses |
| `supported_countermodel` | A single existence theorem combining normalization, monotonicity, nonnegativity, right continuity, support, ratio, error envelope, and eventual positive weighted error |

The pinned environment remains Lean `v4.35.0` and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Replay from the repository root:

```sh
./formalization/lakew build RhCertificates.PrimeObstruction
./formalization/lakew env lean RhCertificates/PrimeSupport.lean
```

Every printed theorem's axiom list is restricted to `propext`, `Classical.choice`,
and `Quot.sound`. No `sorry`, `admit`, added mathematical axiom, unproved desired
sign, or external Python certificate is used. The Mathlib facts used here were
read from the pinned local primary source.

## What remains unproved and the next test

Instantiating the sequence with actual prime powers and discharging (P) and its
support premise are external steps, not a claimed Lean certificate here.
Even after that, the constructed weights would still differ from `Lambda(n)`.
That difference is essential: the result refutes a general deduction from
coarse counting information, not a proposed theorem that actually uses the
exact arithmetic weights or Euler product.

Independent review should check the event convention, first jump, gap endpoint,
PNT-onset conditions, and correspondence between the formal logarithmic integral
and the written `J`. The full second-batch argument has not yet received that
separate review.

The RH-strength unresolved step remains cancellation for the actual
von Mangoldt weights. The next productive proof attempt should identify a
property of those weights which the artificial staircase does not possess and
derive a genuinely one-sided cancellation bound from it. Repeating absolute
PNT estimates or testing more finite intervals does not supply that step.
