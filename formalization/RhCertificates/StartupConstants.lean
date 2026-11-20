module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
Exact coarse bounds for the linear coefficient in the written startup series.
The definition uses Euler's constant, pi and real logarithms. No Python output,
new numerical axiom, or unproved decimal enclosure is imported.
-/

public section
noncomputable section

namespace RhCertificates

@[expose] def startupConstant : ℝ :=
  (Real.eulerMascheroniConstant + Real.pi / 2 + 3 * Real.log 2 + Real.log Real.pi) / 2

theorem startupConstant_eq : startupConstant =
    (Real.eulerMascheroniConstant + Real.pi / 2 + 3 * Real.log 2 + Real.log Real.pi) / 2 := rfl

theorem log_sixtyfour : Real.log (64 : ℝ) = 6 * Real.log 2 := by
  have h := Real.log_pow (2 : ℝ) 6
  norm_num at h
  exact h

theorem gamma_coarse_bounds :
    (569 : ℝ) / 1000 < Real.eulerMascheroniConstant ∧
      Real.eulerMascheroniConstant < 293 / 500 := by
  have hlo := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 63
  have hhi := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 64
  simp only [Real.eulerMascheroniSeq] at hlo
  simp only [Real.eulerMascheroniSeq', OfNat.ofNat_ne_zero, ite_false] at hhi
  norm_num only [Nat.cast_ofNat, show (63 : ℝ) + 1 = 64 by norm_num] at hlo
  norm_num only [Nat.cast_ofNat] at hhi
  rw [log_sixtyfour] at hlo hhi
  have h63 : (4728 : ℝ) / 1000 < (harmonic 63 : ℝ) := by
    norm_num [harmonic, Finset.sum_range_succ]
  have h64 : (harmonic 64 : ℝ) < (4744 : ℝ) / 1000 := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hl := Real.log_two_gt_d9
  have hu := Real.log_two_lt_d9
  constructor <;> linarith

theorem log_pi_coarse_bounds :
    (143 : ℝ) / 125 < Real.log Real.pi ∧ Real.log Real.pi < 229 / 200 := by
  have hlo := Real.sum_range_le_log_div (x := (107 : ℝ) / 207)
    (by norm_num) (by norm_num) 8
  have hhi := Real.log_div_le_sum_range_add (x := (1071 : ℝ) / 2071)
    (by norm_num) (by norm_num) 8
  norm_num [Finset.sum_range_succ] at hlo hhi
  have hlpi : Real.log (157 / 50 : ℝ) < Real.log Real.pi :=
    Real.log_lt_log (by norm_num) (by linarith [Real.pi_gt_d2])
  have hupi : Real.log Real.pi < Real.log (1571 / 500 : ℝ) :=
    Real.log_lt_log Real.pi_pos (lt_trans Real.pi_lt_d4 (by norm_num))
  constructor <;> linarith

theorem startupConstant_bounds :
    (67 : ℝ) / 25 < startupConstant ∧ startupConstant < 2691 / 1000 := by
  have hg := gamma_coarse_bounds
  have hp := log_pi_coarse_bounds
  have hl := Real.log_two_gt_d9
  have hu := Real.log_two_lt_d9
  have hpi_lower := Real.pi_gt_d2
  have hpi_upper := Real.pi_lt_d4
  unfold startupConstant
  constructor <;> linarith

#print axioms startupConstant_eq
#print axioms log_sixtyfour
#print axioms gamma_coarse_bounds
#print axioms log_pi_coarse_bounds
#print axioms startupConstant_bounds

end RhCertificates
