# Independent audit of the convergent Lerch-series bridge

## Outcome and precise scope

The frozen [StartupLerch.lean](../../formalization/RhCertificates/StartupLerch.lean)
source with SHA256
`7883f8d59370eb23a9ebf65fcee79da46d8ce6c5ce18294102d8b0fd4ad3e763`
passed independent mathematical review and source replay. All eleven printed
declarations compiled with only the standard three logical axioms.

**Verification level: kernel-checked identities for the exact defining series
and the reconstructed source expression.** No analytic continuation, Python
value, RH assumption or extra mathematical axiom is used. The fixed real
function `fixedPhi(q)` is defined by its absolutely convergent series on the
needed domain; the module does not pretend to identify a separately defined
general-purpose Lerch function from another library.

The original paper's global RH criterion and zero expansion are outside this
certificate. No novelty or RH proof is claimed.

## Fixed parameters and endpoint convergence

The defined series is exactly

\[
\Phi_*(q)=\sum_{n\ge0}\frac{q^n}{(n+1/4)^2}.
\]

For `0<=q<=1`, the source proves the uniform absolute bound

\[
\left|\frac{q^n}{(n+1/4)^2}\right|\le\frac{16}{(n+1)^2}.
\]

The denominator comparison is valid even at `n=0`, where its factor 16 is
exact. The positive denominator never vanishes at a natural index. The
right-hand side is a summable inverse-square majorant, so the proof includes
`q=1`. Thus subsequent differences of the `q=1` and exponential-parameter
series are justified by actual summability, rather than by subtracting
continued values of divergent series.

For `t>=0`, `q=exp(-2t)` lies in `(0,1]`. The proof therefore covers the
source endpoint `t=0`, with no division by t or differentiated endpoint premise.

## Signs, index shift and exponential cancellation

The correction term is

\[
\frac{e^{-t/2}\Phi_*(e^{-2t})-\Phi_*(1)}4.
\]

The source first identifies it with the sum of a summable difference sequence.
Its zero-index term is **plus** `4*(exp(-t/2)-1)`. Its successor term at `n+1`
is the **negative** of `SmoothSeries.term(n,t)`, with the exact exponent

\[
e^{-t/2}(e^{-2t})^{n+1}=e^{-(2n+5/2)t}.
\]

The denominator normalization is also exact:
`1/(4*(n+1+1/4)^2)=4/(4*n+5)^2`. Hence splitting off the zero-index term
gives the correction as

\[
4(e^{-t/2}-1)-\sum_{n\ge0}\operatorname{term}(n,t).
\]

Adding this to `-4*(exp(t/2)+exp(-t/2)-2)` cancels the negative-exponential
term and leaves `-4*(exp(t/2)-1)`. The subtraction direction, quarter factor
and index shift were all checked; reversing any of them would not give this
identity.

## Coefficient and prime-term identifications

The source uses the real digamma coefficient already proved equal to the
gamma/pi/log `startupConstant`. Its separate complex identity and reality
proof are covered by the [digamma audit](2026-11-19-startup-digamma-independent-audit.md).
Combining that coefficient equality with the cancellation proves
`sourceSmoothExpression(t)=smoothPart(startupConstant,t)` for every `t>=0`.

The prime weight is exactly `vonMangoldt(n)/sqrt(n)`, and its `n=1` value is
proved zero. The reconstructed full expression adds those weights over the
existing explicit cutoff from 2 through `floor(exp(t))`; its equality with
the previously defined full expression is checked for `t>=0`.

At this frozen snapshot, the finite-sum reindexing from a source convention
that starts at 1 is not a declaration in this file. Its omission is explicitly
disclosed in the owner report, rather than silently treated as a formal theorem.
That small normalization step can be supplied separately without changing this
audited source.

## Independent replay and dependencies

```sh
./formalization/lakew env lean RhCertificates/StartupLerch.lean
```

The command exited zero with no warnings. Every listed axiom report contains
exactly `propext`, `Classical.choice`, and `Quot.sound`. There is no `sorryAx`,
native-computation axiom or added mathematical axiom. Evidence:
[startup-lerch-independent-replay.txt](../../formalization/evidence/startup-lerch-independent-replay.txt).
The project pins Lean `leanprover/lean4:v4.35.0` and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

## Remaining step and next test

The exact next integration test is to normalize the source finite sum, rewrite
the resulting source expression with this bridge, and apply the completed
startup negativity certificate on `0<t<=log(2)`. The fixed-parameter defining
series requires no general Lerch analytic-continuation theory for this task.

Beyond that interval the actual prime contribution does not vanish. Its
unbounded-argument cancellation remains unproved, as does any complete
formalization of the paper's RH equivalence. These local identities do not
supply that global result.
