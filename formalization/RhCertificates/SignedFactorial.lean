module

public import Mathlib.Analysis.SpecialFunctions.Stirling
public import RhCertificates.ArithmeticCancellation
import Mathlib.Tactic

/-!
Exact finite summation by parts and Stirling-remainder facts for a signed
factorial attempt. No cancellation estimate for Mobius coefficients or RH
statement is assumed or proved.
-/

public section
noncomputable section

open Finset

namespace RhCertificates.SignedFactorial

def mobiusTail (N : ℕ) (x : ℝ) (d : ℕ) : ℝ :=
  ∑ j ∈ Ioc 0 (N / d), (ArithmeticFunction.moebius j : ℝ) *
    ArithmeticCancellation.kernelWeight x (j * d)

def mobiusCoefficient (N : ℕ) (x : ℝ) (m : ℕ) : ℝ :=
  mobiusTail N x m - mobiusTail N x (m + 1)

theorem mobiusTail_boundary (N : ℕ) (x : ℝ) : mobiusTail N x (N + 1) = 0 := by
  have hdiv : N / (N + 1) = 0 := Nat.div_eq_of_lt (by omega)
  simp [mobiusTail, hdiv]

def smoothMain (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    (n : ℝ) * Real.log n - n + Real.log n / 2 + Real.log (2 * Real.pi) / 2

def remainder (n : ℕ) : ℝ := Real.log (n.factorial : ℝ) - smoothMain n

theorem remainder_zero : remainder 0 = 0 := by norm_num [remainder, smoothMain]

/-- The coefficient at log(1!) is free: changing it shifts the smooth and
remainder pieces oppositely without changing their total factorial cost. -/
theorem unit_split_cancels (c : ℝ) : c * smoothMain 1 + c * remainder 1 = 0 := by
  unfold remainder
  norm_num

theorem remainder_nonneg (n : ℕ) : 0 ≤ remainder n := by
  by_cases hn : n = 0
  · simp [hn, remainder_zero]
  · unfold remainder smoothMain
    rw [ite_eq_right hn]
    exact sub_nonneg.mpr (Stirling.le_log_factorial_stirling hn)

theorem remainder_eq_log_stirlingSeq (n : ℕ) (hn : n ≠ 0) :
    remainder n = Real.log (Stirling.stirlingSeq n) - Real.log Real.pi / 2 := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h := Stirling.log_stirlingSeq_formula n
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnR,
    Real.log_div hnR (Real.exp_ne_zero 1), Real.log_exp] at h
  unfold remainder smoothMain
  rw [ite_eq_right hn, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
  linarith

theorem remainder_step_upper (n : ℕ) (hn : n ≠ 0) :
    remainder n - remainder (n + 1) ≤ 1 / (12 * (n : ℝ) * (n + 1)) := by
  rw [remainder_eq_log_stirlingSeq n hn,
    remainder_eq_log_stirlingSeq (n + 1) (by omega)]
  linarith [Stirling.log_stirlingSeq_sdiff_le n]

theorem remainder_step_nonneg (n : ℕ) :
    0 ≤ remainder (n + 1) - remainder (n + 2) := by
  have h := Stirling.log_stirlingSeq'_antitone (Nat.le_succ n)
  simp only [Function.comp_def, Nat.succ_eq_add_one, Nat.add_assoc] at h
  rw [remainder_eq_log_stirlingSeq (n + 1) (by omega),
    remainder_eq_log_stirlingSeq (n + 2) (by omega)]
  linarith

/-- Exact finite Abel rearrangement, with both boundary terms retained. -/
theorem finite_summation_by_parts (b R : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ range N, (b (k + 1) - b (k + 2)) * R (k + 1)) =
      (∑ k ∈ range N, b (k + 1) * (R (k + 1) - R k)) +
        b 1 * R 0 - b (N + 1) * R N := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [sum_range_succ]
    rw [ih]
    simp only [Nat.add_assoc]
    norm_num only [Nat.reduceAdd]
    ring

theorem signed_remainder_rearrangement (b : ℕ → ℝ) (N : ℕ)
    (hboundary : b (N + 1) = 0) :
    (∑ k ∈ range N, (b (k + 1) - b (k + 2)) * remainder (k + 1)) =
      ∑ k ∈ range N, b (k + 1) * (remainder (k + 1) - remainder k) := by
  rw [finite_summation_by_parts, remainder_zero, hboundary]
  ring

/-- Exact remainder rearrangement for the explicitly defined finite Mobius
coefficients. The full inverse floor-kernel identity is not proved here. -/
theorem canonical_signed_remainder_rearrangement (N : ℕ) (x : ℝ) :
    (∑ k ∈ range N, mobiusCoefficient N x (k + 1) * remainder (k + 1)) =
      ∑ k ∈ range N, mobiusTail N x (k + 1) * (remainder (k + 1) - remainder k) := by
  unfold mobiusCoefficient
  exact signed_remainder_rearrangement (mobiusTail N x) N (mobiusTail_boundary N x)

#print axioms remainder_zero
#print axioms unit_split_cancels
#print axioms mobiusTail_boundary
#print axioms remainder_nonneg
#print axioms remainder_eq_log_stirlingSeq
#print axioms remainder_step_upper
#print axioms remainder_step_nonneg
#print axioms finite_summation_by_parts
#print axioms signed_remainder_rearrangement
#print axioms canonical_signed_remainder_rearrangement

end RhCertificates.SignedFactorial
