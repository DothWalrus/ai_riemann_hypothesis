module

public import RhCertificates.StartupConstants
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
The digamma-quarter identity and the exact identification of its real linear
coefficient with startupConstant. This does not identify a Lerch expression
or the full published screw function with the series defined in this project.
-/

@[expose] public section
noncomputable section

namespace RhCertificates

theorem complex_cot_pi_quarter : Complex.cot ((Real.pi : ℂ) / 4) = 1 := by
  have hr : Real.cot (Real.pi / 4) = 1 := by
    rw [← Real.tan_inv_eq_cot, Real.tan_pi_div_four, inv_one]
  have h := Complex.ofReal_cot (Real.pi / 4)
  simpa only [hr, Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_ofNat] using h.symm

theorem digamma_quarter :
    Complex.digamma ((1 : ℂ) / 4) =
      -(Real.eulerMascheroniConstant : ℂ) - 3 * (Real.log 2 : ℂ) - (Real.pi : ℂ) / 2 := by
  have hnotint : ∀ n : ℤ, (1 / 4 : ℂ) ≠ (n : ℂ) := by
    intro n h
    have hr := congrArg Complex.re h
    norm_num at hr
    have hi : (4 : ℤ) * n = 1 := by
      exact_mod_cast (show (4 : ℝ) * (n : ℝ) = 1 by linarith)
    omega
  have hnotpole : ∀ n : ℕ, 2 * (1 / 4 : ℂ) ≠ -(n : ℂ) := by
    intro n h
    have hr := congrArg Complex.re h
    norm_num at hr
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have href := Complex.digamma_one_sub (s := (1 / 4 : ℂ)) hnotint
  have hdup := Complex.digamma_two_mul (s := (1 / 4 : ℂ)) hnotpole
  norm_num at href hdup
  rw [show (Real.pi : ℂ) * (1 / 4) = (Real.pi : ℂ) / 4 by ring,
    complex_cot_pi_quarter, mul_one] at href
  have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
    exact (Complex.ofReal_log (x := (2 : ℝ)) (by norm_num)).symm
  rw [Complex.digamma_one_half, hlog] at hdup
  rw [href] at hdup
  linear_combination -hdup

theorem digamma_quarter_im : (Complex.digamma ((1 : ℂ) / 4)).im = 0 := by
  rw [digamma_quarter]
  simp only [Complex.sub_im, Complex.neg_im, Complex.mul_im, Complex.ofReal_im,
    Complex.div_ofNat_im]
  norm_num

theorem complex_digamma_coefficient_eq_startupConstant :
    -(Complex.digamma ((1 : ℂ) / 4) - (Real.log Real.pi : ℂ)) / 2 =
      (startupConstant : ℂ) := by
  rw [digamma_quarter, startupConstant_eq]
  push_cast
  ring

def digammaLinearCoefficient : ℝ :=
  -(Complex.digamma ((1 : ℂ) / 4) - (Real.log Real.pi : ℂ)).re / 2

theorem digammaLinearCoefficient_eq_startupConstant :
    digammaLinearCoefficient = startupConstant := by
  rw [digammaLinearCoefficient, digamma_quarter, startupConstant_eq]
  simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.div_ofNat_re]
  norm_num
  ring

#print axioms complex_cot_pi_quarter
#print axioms digamma_quarter
#print axioms digamma_quarter_im
#print axioms complex_digamma_coefficient_eq_startupConstant
#print axioms digammaLinearCoefficient_eq_startupConstant

end RhCertificates
