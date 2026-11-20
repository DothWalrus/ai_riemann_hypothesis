module

public import RhCertificates.SmoothSeries
public import RhCertificates.SmoothDerivatives
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Coarse finite bounds for the displayed series. All finite comparisons are
rational kernel proofs; there is no Python arithmetic premise. -/

@[expose] public section
noncomputable section

namespace RhCertificates.SmoothSeries

theorem exp_quarter_coarse_bounds :
    (321 : ℝ) / 250 ≤ Real.exp ((1 : ℝ) / 4) ∧
      Real.exp ((1 : ℝ) / 4) ≤ 12841 / 10000 := by
  constructor
  · have h := Real.sum_le_exp_of_nonneg (x := (1 : ℝ) / 4) (by norm_num) 6
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith
  · have h := Real.exp_bound' (x := (1 : ℝ) / 4) (by norm_num) (by norm_num)
      (n := 6) (by norm_num)
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith

theorem exp_neg_quarter_coarse_bounds :
    (10000 : ℝ) / 12841 ≤ Real.exp (-(1 : ℝ) / 4) ∧
      Real.exp (-(1 : ℝ) / 4) ≤ 250 / 321 := by
  have h := exp_quarter_coarse_bounds
  rw [show -(1 : ℝ) / 4 = -((1 : ℝ) / 4) by ring, Real.exp_neg, inv_eq_one_div]
  constructor
  · apply (le_div_iff₀ (Real.exp_pos _)).mpr
    nlinarith [h.2]
  · apply (div_le_iff₀ (Real.exp_pos _)).mpr
    nlinarith [h.1]

theorem exponential_half_rate_as_power (n : ℕ) :
    Real.exp (-(rate n * ((1 : ℝ) / 2))) =
      (Real.exp (-(1 : ℝ) / 4)) ^ (4 * n + 5) := by
  rw [← Real.exp_nat_mul, rate_eq]
  congr 1
  push_cast
  ring

theorem smoothPart_half_lt_coarse (C : ℝ) (hC : C ≤ (2691 : ℝ) / 1000) :
    smoothPart C ((1 : ℝ) / 2) < -(1 : ℝ) / 50 := by
  have hx := exp_neg_quarter_coarse_bounds.2
  have hx0 : 0 ≤ Real.exp (-(1 : ℝ) / 4) := (Real.exp_pos _).le
  have hterm (n : ℕ) :
      coefficient n * (1 - ((250 : ℝ) / 321) ^ (4 * n + 5)) ≤ term n ((1 : ℝ) / 2) := by
    rw [term, exponential_half_rate_as_power]
    exact mul_le_mul_of_nonneg_left
      (sub_le_sub_left (pow_le_pow_left₀ hx0 hx _) 1) (coefficient_nonneg n)
  have hsum := Finset.sum_le_sum (s := Finset.range 16) (fun n _ => hterm n)
  have htotal := (summable_term ((1 : ℝ) / 2) (by norm_num)).sum_le_tsum
    (Finset.range 16) (fun n _ => term_nonneg n ((1 : ℝ) / 2) (by norm_num))
  have hfinite : (23 : ℝ) / 100 <
      ∑ n ∈ Finset.range 16, coefficient n * (1 - ((250 : ℝ) / 321) ^ (4 * n + 5)) := by
    norm_num [Finset.sum_range_succ, coefficient]
  have hq := exp_quarter_coarse_bounds.1
  rw [smoothPart_eq]
  norm_num only [div_self, show (1 / 2 : ℝ) / 2 = 1 / 4 by norm_num]
  linarith

theorem coefficient_mul_rate_eq (n : ℕ) :
    coefficient n * rate n = 2 / (4 * (n : ℝ) + 5) := by
  unfold coefficient rate
  have h1 : (4 : ℝ) * ((n : ℝ) + 1) + 1 ≠ 0 := by positivity
  have h2 : (4 : ℝ) * (n : ℝ) + 5 ≠ 0 := by positivity
  field_simp
  ring

theorem derivativeTerm_half_as_power (n : ℕ) :
    derivativeTerm n ((1 : ℝ) / 2) =
      (2 / (4 * (n : ℝ) + 5)) * (Real.exp (-(1 : ℝ) / 4)) ^ (4 * n + 5) := by
  rw [derivativeTerm_eq, coefficient_mul_rate_eq, exponential_half_rate_as_power]

theorem derivativeTerm_half_nonneg (n : ℕ) : 0 ≤ derivativeTerm n ((1 : ℝ) / 2) := by
  rw [derivativeTerm_eq]
  exact mul_nonneg (coefficient_mul_rate_bounds n).1 (Real.exp_pos _).le

theorem derivativeTerm_half_sum_lower :
    (13 : ℝ) / 100 < ∑' n : ℕ, derivativeTerm n ((1 : ℝ) / 2) := by
  have hx := exp_neg_quarter_coarse_bounds.1
  have hx0 : 0 ≤ (10000 : ℝ) / 12841 := by norm_num
  have hterm (n : ℕ) :
      (2 / (4 * (n : ℝ) + 5)) * ((10000 : ℝ) / 12841) ^ (4 * n + 5) ≤
        derivativeTerm n ((1 : ℝ) / 2) := by
    rw [derivativeTerm_half_as_power]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hx _) (by positivity)
  have hsum := Finset.sum_le_sum (s := Finset.range 2) (fun n _ => hterm n)
  have htotal := (derivativeTerm_summable ((1 : ℝ) / 2) (by norm_num)).sum_le_tsum
    (Finset.range 2) (fun n _ => derivativeTerm_half_nonneg n)
  have hfinite : (13 : ℝ) / 100 < ∑ n ∈ Finset.range 2,
      (2 / (4 * (n : ℝ) + 5)) * ((10000 : ℝ) / 12841) ^ (4 * n + 5) := by
    norm_num [Finset.sum_range_succ]
  linarith

theorem derivativeTerm_half_sum_upper :
    (∑' n : ℕ, derivativeTerm n ((1 : ℝ) / 2)) < (3 : ℝ) / 20 := by
  let X : ℝ := 250 / 321
  have hX0 : 0 ≤ X := by norm_num [X]
  have hx := exp_neg_quarter_coarse_bounds.2
  have hx0 : 0 ≤ Real.exp (-(1 : ℝ) / 4) := (Real.exp_pos _).le
  have hq : ‖X ^ 4‖ < 1 := by norm_num [X, Real.norm_eq_abs]
  have hmajor : Summable (fun n : ℕ => ((2 : ℝ) / 13 * X ^ 13) * (X ^ 4) ^ n) :=
    (summable_geometric_of_norm_lt_one hq).mul_left _
  have htail : Summable (fun n : ℕ => derivativeTerm (n + 2) ((1 : ℝ) / 2)) := by
    have hinj : Function.Injective (fun n : ℕ => n + 2) := by
      intro a b h
      change a + 2 = b + 2 at h
      omega
    exact (derivativeTerm_summable ((1 : ℝ) / 2) (by norm_num)).comp_injective hinj
  have hterm (n : ℕ) : derivativeTerm (n + 2) ((1 : ℝ) / 2) ≤
      ((2 : ℝ) / 13 * X ^ 13) * (X ^ 4) ^ n := by
    rw [derivativeTerm_half_as_power]
    have hc : (2 : ℝ) / (4 * ((n + 2 : ℕ) : ℝ) + 5) ≤ 2 / 13 := by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      apply (div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 13)).mpr
      push_cast
      linarith
    have hp := pow_le_pow_left₀ hx0 hx (4 * (n + 2) + 5)
    have hpower : X ^ (4 * (n + 2) + 5) = X ^ 13 * (X ^ 4) ^ n := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    calc
      _ ≤ ((2 : ℝ) / 13) * X ^ (4 * (n + 2) + 5) :=
        mul_le_mul hc hp (by positivity) (by norm_num)
      _ = _ := by rw [hpower]; ring
  have htail_bound := htail.tsum_le_tsum hterm hmajor
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hq] at htail_bound
  have hsplit := (derivativeTerm_summable ((1 : ℝ) / 2) (by norm_num)).sum_add_tsum_nat_add 2
  have h0 : derivativeTerm 0 ((1 : ℝ) / 2) ≤ (2 / 5 : ℝ) * X ^ 5 := by
    rw [derivativeTerm_half_as_power]
    convert mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hx 5)
      (show (0 : ℝ) ≤ 2 / 5 by norm_num) using 1 <;> norm_num
  have h1 : derivativeTerm 1 ((1 : ℝ) / 2) ≤ (2 / 9 : ℝ) * X ^ 9 := by
    rw [derivativeTerm_half_as_power]
    convert mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hx 9)
      (show (0 : ℝ) ≤ 2 / 9 by norm_num) using 1 <;> norm_num
  have hfinite : (2 / 5 : ℝ) * X ^ 5 + (2 / 9 : ℝ) * X ^ 9 +
      ((2 : ℝ) / 13 * X ^ 13) * (1 - X ^ 4)⁻¹ < (3 : ℝ) / 20 := by
    norm_num [X]
  norm_num [Finset.sum_range_succ] at hsplit
  linarith

theorem smoothDerivative_half_coarse_bounds (C : ℝ)
    (hClo : (67 : ℝ) / 25 < C) (hChi : C < (2691 : ℝ) / 1000) :
    -(1 : ℝ) / 25 < smoothDerivative C ((1 : ℝ) / 2) ∧
      smoothDerivative C ((1 : ℝ) / 2) < 0 := by
  have hq := exp_quarter_coarse_bounds
  have hl := derivativeTerm_half_sum_lower
  have hu := derivativeTerm_half_sum_upper
  rw [smoothDerivative_eq]
  norm_num only [show (1 / 2 : ℝ) / 2 = 1 / 4 by norm_num]
  constructor <;> linarith

#print axioms exp_quarter_coarse_bounds
#print axioms exp_neg_quarter_coarse_bounds
#print axioms exponential_half_rate_as_power
#print axioms smoothPart_half_lt_coarse
#print axioms coefficient_mul_rate_eq
#print axioms derivativeTerm_half_as_power
#print axioms derivativeTerm_half_nonneg
#print axioms derivativeTerm_half_sum_lower
#print axioms derivativeTerm_half_sum_upper
#print axioms smoothDerivative_half_coarse_bounds

end RhCertificates.SmoothSeries
