module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
Arithmetic component of the startup tangent argument.

This theorem assumes the tangent's intercept and slope bounds. It does
not prove those bounds for the actual Nakamura--Suzuki function, nor
the analytic supporting-tangent or convex-chord inequalities.
-/

public section

namespace RhCertificates

theorem tangent_negative
    (h d t : ℝ)
    (hh : h < -(1 : ℝ) / 40)
    (hd_lower : -(1 : ℝ) / 32 < d)
    (hd_upper : d < 0)
    (ht : (1 : ℝ) / 4 ≤ t) :
    h + d * (t - (1 : ℝ) / 2) < 0 := by
  by_cases ht_half : (1 : ℝ) / 2 ≤ t
  · have hproduct : d * (t - (1 : ℝ) / 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_lt hd_upper)
        (sub_nonneg.mpr ht_half)
    linarith
  · have hnegative : t - (1 : ℝ) / 2 ≤ 0 := by linarith
    have hproduct := mul_le_mul_of_nonpos_right (le_of_lt hd_lower) hnegative
    nlinarith

#print axioms tangent_negative

end RhCertificates
