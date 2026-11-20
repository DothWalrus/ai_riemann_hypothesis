# Independent audit of the signed factorial attempt

## Outcome and exact verification level

[SignedFactorial.lean](../../formalization/RhCertificates/SignedFactorial.lean)
and [the attempt report](2026-11-19-signed-factorial-attempt-agent.md) pass this
independent mathematical review and source replay. All ten printed declarations
compile successfully with only `propext`, `Classical.choice`, and `Quot.sound`.

This is a **failed global proof attempt** with useful checked bookkeeping.
The finite Abel identities and actual Stirling remainder facts are
kernel-checked. The full finite Möbius inversion and the displayed coarse
square-root error estimate remain written derivations, not Lean certificates.
No improved one-sided estimate for the actual J, S or g is proved, and no RH
proof, new criterion, or novelty is claimed.

## Finite inversion: written argument checked

For x>1 and N=floor(x), the proposed coefficients are

    b_d=sum(j<=N/d) mu(j)*w_x(jd),    a_m=b_m-b_(m+1).

The terminal value b_(N+1)=0 follows directly from N/(N+1)=0, including N=0.
For 1<=d<=N, summing a_m floor(m/d) by parts reduces to the sum of b_(jd)
over positive j<=N/d. Substituting b and grouping the finite pairs by their
product gives the coefficient sum of mu(k) over k dividing that product.
The divisor sum is one for product 1 and zero otherwise, leaving w_x(d).
The stated domain d>=1 is necessary and is retained. There is no rearrangement
of an infinite series or continued Mellin value in this step.

Using the already formalized factorial-floor identity then gives the written
signed factorial representation of S. The new SignedFactorial module does
not claim to have compiled this full Möbius-inversion derivation.

## Abel boundary audit

For arbitrary b and R the compiled identity is

    sum(m=1..N) (b_m-b_(m+1))*R_m
      =sum(m=1..N) b_m*(R_m-R_(m-1)) + b_1*R_0-b_(N+1)*R_N.

Both endpoint terms are correct. Setting R_0=0 and b_(N+1)=0 gives the
canonical remainder identity, whose first term is b_1*r_1 and whose remaining
terms start at m=2. The proof does not silently drop a nonzero first-order
endpoint, and it also handles the empty finite range.

## Actual Stirling remainder audit

For n>=1 the defined smooth term is

    M_n=(n+1/2)*log(n)-n+log(2*pi)/2,

with M_0=0 and r_n=log(n!)-M_n. Thus r_0=0 and
r_1=1-log(2*pi)/2. The definition agrees with the report.

The source proves r_n=log(stirlingSeq(n))-log(pi)/2 for n>=1, using the
actual Mathlib definition and its logarithmic formula. It then obtains
nonnegativity and monotone decrease for n>=1. Its upper step bound

    r_n-r_(n+1)<=1/(12*n*(n+1)),  n>=1,

comes directly from Mathlib's proved `log_stirlingSeq_sdiff_le` theorem.
This is a genuine stepwise bound. It is not an invalid subtraction of two
independent upper bounds on individual remainders. The nonnegative step lemma
also has the correct index offset: it compares r_(n+1) and r_(n+2), leaving
the exceptional transition from r_0=0 to r_1>0 outside that claim.

## Written absolute estimate and its constant

For y>=1 the function log(y/u)/sqrt(u) is nonnegative and decreasing on [1,y].
The monotone sum-integral estimate gives

    sum(j<=y) log(y/j)/sqrt(j)
      <=log(y)+integral(1..y) log(y/u)/sqrt(u) du
      =4sqrt(y)-log(y)-4<=4sqrt(y).

Factoring out 1/sqrt(m), and using |mu(j)|<=1, proves the stated written bound
|b_m|<=4sqrt(x)/m for 1<=m<=N. The floor cutoff is compatible with y=x/m.

The absolute Abel bound is therefore

    |R_x|<=4sqrt(x)*r_1
      +(sqrt(x)/3)*sum(m=2..N) 1/(m^2*(m-1)).

The remaining sum is at most 1, for example by comparison with the telescoping
sum of 1/(m*(m-1)). Hence the report's coefficient
`(4r_1+1/3)*sqrt(x)` is safe. This is a written mathematical estimate; its
sum-integral step is explicitly not presented as kernel-certified. A
square-root-sized absolute bound does not provide the missing cancellation.

## Unit coefficient and diagnostic transform

The coefficient a_1 is free for the actual factorial cost because log(1!)=0,
and changing its kernel value at d=1 does not affect the sum against Lambda,
since Lambda(1)=0. It would not be free if one demanded literal kernel matching
also at d=1. The report correctly limits the freedom to the actual weighted
cost and distinguishes it from the stated canonical choice.

Changing a_1 shifts the smooth and remainder pieces by opposite amounts;
the compiled `unit_split_cancels` theorem verifies this. Consequently the
isolated remainder estimate cannot be promoted into an obstruction to every
possible signed representation.

The written diagnostic Mellin transform is valid initially for Re(s)>1/2:
absolute convergence permits integration of each log(y/j) term, giving
`1/(s^2*zeta(s+1/2))`. An **absolute** subpower bound
`|B(y)|<=C_epsilon*y^epsilon` for every epsilon>0 would make the ordinary
transform holomorphic for Re(s)>0 and therefore already exclude the missing
right-of-critical-line zeros. The author was asked to state this absolute
form explicitly. It is a diagnostic warning against assuming RH-strength
cancellation, not an extra theorem used by the formal proof.

## Independent replay and remaining step

Independent command from the repository root, exit zero:

```sh
./formalization/lakew env lean RhCertificates/SignedFactorial.lean
```

Reviewed source SHA-256:
`7547f2b02e2502993eff5dd29921b9b6d085256d4d423c4f4ab59ce565309bc5`.
Unique independent evidence is
[signed-factorial-independent-replay.txt](../../formalization/evidence/signed-factorial-independent-replay.txt).
The owner evidence is
[signed-factorial-build.txt](../../formalization/evidence/signed-factorial-build.txt).

No mathematical axiom asserting cancellation, numerical input, unfinished
proof or native-computation axiom appears in the replayed statements.
The exact unresolved step is a one-sided estimate for the combined signed
smooth and remainder terms using actual arithmetic cancellation. Fixing a_1
normalizes the irrelevant freedom; it does not supply that estimate. The next
test must state the proposed new arithmetic bound explicitly and check that it
has not merely restated the original sign problem.
