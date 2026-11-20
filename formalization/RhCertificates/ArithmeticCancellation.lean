module

public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Analysis.SpecialFunctions.Log.Sum
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
Obstructions to an exact positive factorial-floor decomposition of the
project kernel. Actual logarithmic-weight bounds are proved analytically
inside Lean; no Python interval output is imported as a hypothesis.
-/

public section
noncomputable section

open Finset

namespace RhCertificates.ArithmeticCancellation

/-- Existing von Mangoldt divisor identity, summed to the factorial identity
before the standard finite floor-sum reindexing. This is prior art. -/
theorem mangoldt_divisor_total (N : ℕ) :
    (∑ n ∈ Ioc 0 N, ∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d) =
      Real.log (N.factorial : ℝ) := by
  calc
    _ = ∑ n ∈ Ioc 0 N, Real.log (n : ℝ) := by
      apply sum_congr rfl
      intro n _
      exact ArithmeticFunction.vonMangoldt_sum
    _ = _ := Real.sum_log_eq_log_factorial N

def selectedPrimePowers : Finset ℕ := {2, 3, 5, 8, 9, 13}

def dualWeight (w : ℕ → ℝ) : ℝ := w 2 - w 3 - w 5 - w 8 + w 9 + w 13

def floorRepresentation16 (a w : ℕ → ℝ) : Prop :=
  ∀ d ∈ selectedPrimePowers,
    w d = ∑ m ∈ range 17, a m * ((m / d : ℕ) : ℝ)

theorem dual_floor_identity (a w : ℕ → ℝ) (h : floorRepresentation16 a w) :
    dualWeight w = a 2 + a 4 + a 13 + 2 * a 14 := by
  have h2 := h 2 (by norm_num [selectedPrimePowers])
  have h3 := h 3 (by norm_num [selectedPrimePowers])
  have h5 := h 5 (by norm_num [selectedPrimePowers])
  have h8 := h 8 (by norm_num [selectedPrimePowers])
  have h9 := h 9 (by norm_num [selectedPrimePowers])
  have h13 := h 13 (by norm_num [selectedPrimePowers])
  norm_num [sum_range_succ] at h2 h3 h5 h8 h9 h13
  unfold dualWeight
  linarith

theorem dual_nonneg_of_nonneg_representation (a w : ℕ → ℝ)
    (ha : ∀ m ∈ range 17, 0 ≤ a m) (h : floorRepresentation16 a w) :
    0 ≤ dualWeight w := by
  rw [dual_floor_identity a w h]
  have h2 := ha 2 (by norm_num)
  have h4 := ha 4 (by norm_num)
  have h13 := ha 13 (by norm_num)
  have h14 := ha 14 (by norm_num)
  linarith

theorem dual_negative_of_enclosures (w : ℕ → ℝ)
    (h2 : w 2 ≤ (1471 : ℝ) / 1000)
    (h3 : (966 : ℝ) / 1000 ≤ w 3)
    (h5 : (520 : ℝ) / 1000 ≤ w 5)
    (h8 : (245 : ℝ) / 1000 ≤ w 8)
    (h9 : w 9 ≤ (192 : ℝ) / 1000)
    (h13 : w 13 ≤ (58 : ℝ) / 1000) :
    dualWeight w ≤ -(1 : ℝ) / 100 := by
  unfold dualWeight
  linarith

theorem no_nonnegative_floor_representation_of_enclosures (w : ℕ → ℝ)
    (h2 : w 2 ≤ (1471 : ℝ) / 1000)
    (h3 : (966 : ℝ) / 1000 ≤ w 3)
    (h5 : (520 : ℝ) / 1000 ≤ w 5)
    (h8 : (245 : ℝ) / 1000 ≤ w 8)
    (h9 : w 9 ≤ (192 : ℝ) / 1000)
    (h13 : w 13 ≤ (58 : ℝ) / 1000) :
    ¬ ∃ a : ℕ → ℝ, (∀ m ∈ range 17, 0 ≤ a m) ∧ floorRepresentation16 a w := by
  rintro ⟨a, ha, h⟩
  have hlo := dual_nonneg_of_nonneg_representation a w ha h
  have hhi := dual_negative_of_enclosures w h2 h3 h5 h8 h9 h13
  linarith

def actualWeight16 (d : ℕ) : ℝ := Real.log (16 / (d : ℝ)) / Real.sqrt (d : ℝ)

private theorem log8_upper : Real.log 8 ≤ (20799 : ℝ) / 10000 := by
  have h := Real.log_div_le_sum_range_add (x := (7 : ℝ) / 9) (by norm_num) (by norm_num) 20
  norm_num [sum_range_succ] at h
  linarith

private theorem log16_div3_lower : (3347 : ℝ) / 2000 ≤ Real.log ((16 : ℝ) / 3) := by
  have h := Real.sum_range_le_log_div (x := (13 : ℝ) / 19) (by norm_num) (by norm_num) 10
  norm_num [sum_range_succ] at h
  linarith

private theorem log16_div5_lower : (1163 : ℝ) / 1000 ≤ Real.log ((16 : ℝ) / 5) := by
  have h := Real.sum_range_le_log_div (x := (11 : ℝ) / 21) (by norm_num) (by norm_num) 6
  norm_num [sum_range_succ] at h
  linarith

private theorem log2_lower : (6931 : ℝ) / 10000 ≤ Real.log 2 := by
  have h := Real.sum_range_le_log_div (x := (1 : ℝ) / 3) (by norm_num) (by norm_num) 4
  norm_num [sum_range_succ] at h
  linarith

private theorem log16_div9_upper : Real.log ((16 : ℝ) / 9) ≤ (72 : ℝ) / 125 := by
  have h := Real.log_div_le_sum_range_add (x := (7 : ℝ) / 25) (by norm_num) (by norm_num) 3
  norm_num [sum_range_succ] at h
  linarith

private theorem log16_div13_upper : Real.log ((16 : ℝ) / 13) ≤ (417 : ℝ) / 2000 := by
  have h := Real.log_div_le_sum_range_add (x := (3 : ℝ) / 29) (by norm_num) (by norm_num) 2
  norm_num [sum_range_succ] at h
  linarith

theorem actualWeight16_enclosures :
    actualWeight16 2 ≤ (1471 : ℝ) / 1000 ∧
    (966 : ℝ) / 1000 ≤ actualWeight16 3 ∧
    (520 : ℝ) / 1000 ≤ actualWeight16 5 ∧
    (245 : ℝ) / 1000 ≤ actualWeight16 8 ∧
    actualWeight16 9 ≤ (192 : ℝ) / 1000 ∧
    actualWeight16 13 ≤ (58 : ℝ) / 1000 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Real.log (16 / (2 : ℝ)) / Real.sqrt 2 ≤ _
    norm_num only [Nat.cast_ofNat, show (16 : ℝ) / 2 = 8 by norm_num]
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))).mpr
    have hs : (707 : ℝ) / 500 ≤ Real.sqrt 2 := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    linarith [log8_upper]
  · change _ ≤ Real.log (16 / (3 : ℝ)) / Real.sqrt 3
    apply (le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))).mpr
    have hs : Real.sqrt 3 ≤ (17321 : ℝ) / 10000 := by
      rw [Real.sqrt_le_iff]
      norm_num
    linarith [log16_div3_lower]
  · change _ ≤ Real.log (16 / (5 : ℝ)) / Real.sqrt 5
    apply (le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5))).mpr
    have hs : Real.sqrt 5 ≤ (22361 : ℝ) / 10000 := by
      rw [Real.sqrt_le_iff]
      norm_num
    linarith [log16_div5_lower]
  · change _ ≤ Real.log (16 / (8 : ℝ)) / Real.sqrt 8
    norm_num only [show (16 : ℝ) / 8 = 2 by norm_num]
    apply (le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 8))).mpr
    have hs : Real.sqrt 8 ≤ (5657 : ℝ) / 2000 := by
      rw [Real.sqrt_le_iff]
      norm_num
    linarith [log2_lower]
  · change Real.log (16 / (9 : ℝ)) / Real.sqrt 9 ≤ _
    norm_num
    linarith [log16_div9_upper]
  · change Real.log (16 / (13 : ℝ)) / Real.sqrt 13 ≤ _
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 13))).mpr
    have hs : (18 : ℝ) / 5 ≤ Real.sqrt 13 := by
      nlinarith [Real.sqrt_nonneg (13 : ℝ), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)]
    linarith [log16_div13_upper]

theorem no_nonnegative_actual_floor_representation :
    ¬ ∃ a : ℕ → ℝ, (∀ m ∈ range 17, 0 ≤ a m) ∧ floorRepresentation16 a actualWeight16 := by
  rcases actualWeight16_enclosures with ⟨h2, h3, h5, h8, h9, h13⟩
  exact no_nonnegative_floor_representation_of_enclosures actualWeight16 h2 h3 h5 h8 h9 h13

theorem binary_floor_inequality (m : ℕ) :
    2 * ((m / 4 : ℕ) : ℝ) ≤ ((m / 2 : ℕ) : ℝ) := by
  have h : 2 * (m / 4) ≤ m / 2 := by omega
  exact_mod_cast h

theorem binary_weight_necessary (T : Finset ℕ) (a : ℕ → ℝ)
    (ha : ∀ m ∈ T, 0 ≤ a m) :
    2 * (∑ m ∈ T, a m * ((m / 4 : ℕ) : ℝ)) ≤
      ∑ m ∈ T, a m * ((m / 2 : ℕ) : ℝ) := by
  rw [mul_sum]
  apply sum_le_sum
  intro m hm
  calc
    2 * (a m * ((m / 4 : ℕ) : ℝ)) = a m * (2 * ((m / 4 : ℕ) : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (binary_floor_inequality m) (ha m hm)

def kernelWeight (x : ℝ) (d : ℕ) : ℝ := Real.log (x / (d : ℝ)) / Real.sqrt (d : ℝ)

theorem binary_actual_weight_violation : kernelWeight 32 2 < 2 * kernelWeight 32 4 := by
  have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 4 using 1
    norm_num
  have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 3 using 1
    norm_num
  have hright : 2 * kernelWeight 32 4 = Real.log (8 : ℝ) := by
    norm_num [kernelWeight]
    ring
  rw [hright]
  change Real.log (32 / (2 : ℝ)) / Real.sqrt 2 < Real.log (8 : ℝ)
  norm_num only [show (32 : ℝ) / 2 = 16 by norm_num]
  rw [h16, h8]
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  apply (div_lt_iff₀ hs).mpr
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hroot : 4 < 3 * Real.sqrt (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  nlinarith [mul_pos hlog (sub_pos.mpr hroot)]

/-- No exact nonnegative floor-kernel representation can match the actual
weights at 2 and 4 when x=32, even with arbitrary finite index support. -/
theorem no_nonnegative_actual_floor_representation32 (T : Finset ℕ) :
    ¬ ∃ a : ℕ → ℝ, (∀ m ∈ T, 0 ≤ a m) ∧
      kernelWeight 32 2 = (∑ m ∈ T, a m * ((m / 2 : ℕ) : ℝ)) ∧
      kernelWeight 32 4 = (∑ m ∈ T, a m * ((m / 4 : ℕ) : ℝ)) := by
  rintro ⟨a, ha, h2, h4⟩
  have h := binary_weight_necessary T a ha
  rw [← h2, ← h4] at h
  exact not_le_of_gt binary_actual_weight_violation h

theorem binary_kernel_difference (x : ℝ) (hx : 0 < x) :
    kernelWeight x 2 - 2 * kernelWeight x 4 =
      (1 / Real.sqrt 2 - 1) * Real.log x + (2 - 1 / Real.sqrt 2) * Real.log 2 := by
  have hlog2 := Real.log_div hx.ne' (show (2 : ℝ) ≠ 0 by norm_num)
  have hlog4 := Real.log_div hx.ne' (show (4 : ℝ) ≠ 0 by norm_num)
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 2 using 1
    norm_num
  unfold kernelWeight
  norm_num only [Nat.cast_ofNat]
  rw [hlog2, hlog4, h4]
  norm_num
  ring

theorem binary_actual_weight_violation_of_large (x : ℝ) (hx : 32 ≤ x) :
    kernelWeight x 2 < 2 * kernelWeight x 4 := by
  have hxpos : 0 < x := by linarith
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs1 : 1 < Real.sqrt (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hc : 1 / Real.sqrt (2 : ℝ) - 1 < 0 := by
    have h : 1 / Real.sqrt (2 : ℝ) < 1 := (div_lt_one hs).mpr hs1
    linarith
  have hlog := Real.log_le_log (show (0 : ℝ) < 32 by norm_num) hx
  have hmono := mul_le_mul_of_nonpos_left hlog hc.le
  have hbase : kernelWeight 32 2 - 2 * kernelWeight 32 4 < 0 := by
    linarith [binary_actual_weight_violation]
  have hdiffx := binary_kernel_difference x hxpos
  have hdiff32 := binary_kernel_difference 32 (by norm_num : (0 : ℝ) < 32)
  linarith

#print axioms mangoldt_divisor_total
#print axioms dual_floor_identity
#print axioms dual_nonneg_of_nonneg_representation
#print axioms dual_negative_of_enclosures
#print axioms no_nonnegative_floor_representation_of_enclosures
#print axioms actualWeight16_enclosures
#print axioms no_nonnegative_actual_floor_representation
#print axioms binary_floor_inequality
#print axioms binary_weight_necessary
#print axioms binary_actual_weight_violation
#print axioms no_nonnegative_actual_floor_representation32
#print axioms binary_kernel_difference
#print axioms binary_actual_weight_violation_of_large

end RhCertificates.ArithmeticCancellation
