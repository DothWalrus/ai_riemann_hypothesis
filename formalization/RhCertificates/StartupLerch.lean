module

public import RhCertificates.StartupDigamma
public import RhCertificates.SmoothSeries
public import RhCertificates.PrimeStartup
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

/-!
The fixed absolutely convergent defining series Phi(q,2,1/4), and the exact
source-expression to smooth-series identity on t>=0. No analytic continuation
or global RH equivalence is used.
-/

@[expose] public section
noncomputable section

namespace RhCertificates.StartupLerch

def phiTerm (q : ℝ) (n : ℕ) : ℝ := q ^ n / ((n : ℝ) + 1 / 4) ^ 2

def fixedPhi (q : ℝ) : ℝ := ∑' n : ℕ, phiTerm q n

theorem norm_phiTerm_le (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) :
    ‖phiTerm q n‖ ≤ 16 * (1 / ((n : ℝ) + 1) ^ 2) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hden : 0 < ((n : ℝ) + 1 / 4) ^ 2 := by positivity
  have hdom : 0 < ((n : ℝ) + 1) ^ 2 := by positivity
  have hqpow : q ^ n ≤ 1 := pow_le_one₀ hq0 hq1
  have hp : 0 ≤ q ^ n := pow_nonneg hq0 n
  rw [phiTerm, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hp hden.le)]
  have hfirst := div_le_div_of_nonneg_right hqpow hden.le
  apply hfirst.trans
  rw [← mul_div_assoc, mul_one]
  apply (div_le_div_iff₀ hden hdom).mpr
  nlinarith

theorem summable_phiTerm (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Summable (phiTerm q) :=
  (SmoothSeries.summable_dominator.mul_left 16).of_norm_bounded
    (fun n => norm_phiTerm_le q hq0 hq1 n)

def lerchDifferenceTerm (t : ℝ) (n : ℕ) : ℝ :=
  (Real.exp (-t / 2) * phiTerm (Real.exp (-(2 * t))) n - phiTerm 1 n) / 4

theorem lerchDifferenceTerm_summable (t : ℝ) (ht : 0 ≤ t) :
    Summable (lerchDifferenceTerm t) := by
  have hq := summable_phiTerm (Real.exp (-(2 * t))) (Real.exp_pos _).le
    (Real.exp_le_one_iff.mpr (by linarith))
  exact ((hq.mul_left (Real.exp (-t / 2))).sub
    (summable_phiTerm 1 (by norm_num) le_rfl)).div_const 4

theorem lerchDifference_tsum (t : ℝ) (ht : 0 ≤ t) :
    (∑' n : ℕ, lerchDifferenceTerm t n) =
      (Real.exp (-t / 2) * fixedPhi (Real.exp (-(2 * t))) - fixedPhi 1) / 4 := by
  have hq := summable_phiTerm (Real.exp (-(2 * t))) (Real.exp_pos _).le
    (Real.exp_le_one_iff.mpr (by linarith))
  have h1 := summable_phiTerm 1 (by norm_num) le_rfl
  simp only [lerchDifferenceTerm, tsum_div_const, Summable.tsum_sub
    (hq.mul_left (Real.exp (-t / 2))) h1, tsum_mul_left, fixedPhi]

theorem lerchDifferenceTerm_zero (t : ℝ) :
    lerchDifferenceTerm t 0 = 4 * (Real.exp (-t / 2) - 1) := by
  norm_num [lerchDifferenceTerm, phiTerm]
  ring

theorem exponential_rate_identity (n : ℕ) (t : ℝ) :
    Real.exp (-t / 2) * Real.exp (-(2 * t)) ^ (n + 1) =
      Real.exp (-(SmoothSeries.rate n * t)) := by
  rw [← Real.exp_nat_mul, ← Real.exp_add, SmoothSeries.rate_eq]
  congr 1
  push_cast
  ring

theorem lerchDifferenceTerm_succ (t : ℝ) (n : ℕ) :
    lerchDifferenceTerm t (n + 1) = -SmoothSeries.term n t := by
  rw [lerchDifferenceTerm, phiTerm, phiTerm]
  simp only [one_pow]
  rw [← mul_div_assoc, exponential_rate_identity]
  unfold SmoothSeries.term
  rw [SmoothSeries.coefficient_eq_written]
  push_cast
  field_simp
  ring

theorem lerchDifference_eq (t : ℝ) (ht : 0 ≤ t) :
    (Real.exp (-t / 2) * fixedPhi (Real.exp (-(2 * t))) - fixedPhi 1) / 4 =
      4 * (Real.exp (-t / 2) - 1) - ∑' n : ℕ, SmoothSeries.term n t := by
  have hsplit := (lerchDifferenceTerm_summable t ht).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, lerchDifferenceTerm_zero,
    lerchDifferenceTerm_succ, tsum_neg] at hsplit
  rw [lerchDifference_tsum t ht] at hsplit
  linarith

def sourceSmoothExpression (t : ℝ) : ℝ :=
  -4 * (Real.exp (t / 2) + Real.exp (-t / 2) - 2) +
    digammaLinearCoefficient * t +
    (Real.exp (-t / 2) * fixedPhi (Real.exp (-(2 * t))) - fixedPhi 1) / 4

theorem sourceSmoothExpression_eq_smoothPart (t : ℝ) (ht : 0 ≤ t) :
    sourceSmoothExpression t = SmoothSeries.smoothPart startupConstant t := by
  rw [sourceSmoothExpression, lerchDifference_eq t ht,
    digammaLinearCoefficient_eq_startupConstant, SmoothSeries.smoothPart_eq]
  ring

def actualPrimeWeight (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)

theorem actualPrimeWeight_one : actualPrimeWeight 1 = 0 := by
  simp [actualPrimeWeight]

def sourceFullExpression (t : ℝ) : ℝ :=
  sourceSmoothExpression t + PrimeStartup.primeContribution actualPrimeWeight t

theorem sourceFullExpression_eq_fullExpression (t : ℝ) (ht : 0 ≤ t) :
    sourceFullExpression t =
      PrimeStartup.fullExpression startupConstant actualPrimeWeight t := by
  rw [sourceFullExpression, sourceSmoothExpression_eq_smoothPart t ht,
    PrimeStartup.fullExpression]

#print axioms norm_phiTerm_le
#print axioms summable_phiTerm
#print axioms lerchDifferenceTerm_summable
#print axioms lerchDifference_tsum
#print axioms lerchDifferenceTerm_zero
#print axioms exponential_rate_identity
#print axioms lerchDifferenceTerm_succ
#print axioms lerchDifference_eq
#print axioms sourceSmoothExpression_eq_smoothPart
#print axioms actualPrimeWeight_one
#print axioms sourceFullExpression_eq_fullExpression

end RhCertificates.StartupLerch
