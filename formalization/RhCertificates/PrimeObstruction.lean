module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

/-!
An artificial, non-arithmetic model illustrating an obstruction in a
prime-error-bound argument. These functions are not Chebyshev's function,
the Riemann zeta function, or the Nakamura--Suzuki screw function.
-/

public section

noncomputable section

namespace RhCertificates.PrimeObstruction

def modelPsi (t : ℝ) : ℝ := Real.exp t + Real.exp (3 * t / 4) - 2

def modelError (t : ℝ) : ℝ := Real.exp (3 * t / 4) - 2

def modelWeightedError (t : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..t,
    (Real.exp (v / 4) - 2 * Real.exp (-v / 2)) * (1 + (t - v) / 2)

theorem modelPsi_zero : modelPsi 0 = 0 := by
  norm_num [modelPsi]

theorem modelPsi_monotone : Monotone modelPsi := by
  intro s t hst
  have hfirst := Real.exp_le_exp.mpr hst
  have hsecond := Real.exp_le_exp.mpr (show 3 * s / 4 ≤ 3 * t / 4 by linarith)
  simp only [modelPsi]
  linarith

theorem modelPsi_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ modelPsi t := by
  simpa only [modelPsi_zero] using modelPsi_monotone ht

theorem modelPsi_sub_exp (t : ℝ) : modelPsi t - Real.exp t = modelError t := by
  simp only [modelPsi, modelError]
  ring

theorem modelError_abs_le (t : ℝ) (ht : 0 ≤ t) :
    |modelError t| ≤ Real.exp (3 * t / 4) := by
  have h := Real.one_le_exp (show 0 ≤ 3 * t / 4 by linarith)
  rw [modelError, abs_le]
  constructor <;> linarith

theorem modelError_relative_abs_le (t : ℝ) (ht : 0 ≤ t) :
    |modelError t| / Real.exp t ≤ Real.exp (-t / 4) := by
  have h := div_le_div_of_nonneg_right (modelError_abs_le t ht) (Real.exp_pos t).le
  have he : Real.exp (3 * t / 4) / Real.exp t = Real.exp (-t / 4) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  simpa only [he] using h

theorem modelError_pnt_envelope (c v : ℝ) (hc : 0 ≤ c) (hv : 4 * c ≤ v) :
    |modelError (v ^ 2)| ≤ Real.exp (v ^ 2 - c * v) := by
  apply (modelError_abs_le (v ^ 2) (sq_nonneg v)).trans
  apply Real.exp_le_exp.mpr
  have hv0 : 0 ≤ v := by linarith
  nlinarith [mul_nonneg hv0 (sub_nonneg.mpr hv)]

private def modelPrimitive (t v : ℝ) : ℝ :=
  Real.exp (v / 4) * (12 + 2 * t - 2 * v) -
    2 * ((v - t) * Real.exp (-v / 2))

theorem modelWeightedError_eq_convolution (t : ℝ) :
    modelWeightedError t = ∫ v in (0 : ℝ)..t,
      (modelPsi v - Real.exp v) * Real.exp (-v / 2) * (1 + (t - v) / 2) := by
  unfold modelWeightedError
  apply intervalIntegral.integral_congr
  intro v _
  dsimp only
  have he : Real.exp (3 * v / 4) * Real.exp (-v / 2) = Real.exp (v / 4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [modelPsi_sub_exp]
  dsimp [modelError]
  calc
    (Real.exp (v / 4) - 2 * Real.exp (-v / 2)) * (1 + (t - v) / 2) =
        (Real.exp (3 * v / 4) * Real.exp (-v / 2) - 2 * Real.exp (-v / 2)) *
          (1 + (t - v) / 2) := by rw [he]
    _ = _ := by ring

private theorem modelPrimitive_hasDerivAt (t v : ℝ) :
    HasDerivAt (modelPrimitive t)
      ((Real.exp (v / 4) - 2 * Real.exp (-v / 2)) * (1 + (t - v) / 2)) v := by
  have he1 := ((hasDerivAt_id v).div_const 4).exp
  have he2 := (((hasDerivAt_id v).neg).div_const 2).exp
  have hp := (hasDerivAt_const v (12 + 2 * t)).sub ((hasDerivAt_id v).const_mul 2)
  have hq := (hasDerivAt_id v).sub_const t
  convert (he1.mul hp).sub ((hq.mul he2).const_mul 2) using 1
  · funext x
    dsimp [modelPrimitive]
  · dsimp
    ring

theorem modelWeightedError_eq (t : ℝ) :
    modelWeightedError t = 12 * Real.exp (t / 4) - 12 - 4 * t := by
  have hint : IntervalIntegrable
      (fun v : ℝ => (Real.exp (v / 4) - 2 * Real.exp (-v / 2)) *
        (1 + (t - v) / 2)) MeasureTheory.volume 0 t := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v _ => modelPrimitive_hasDerivAt t v) hint
  calc
    modelWeightedError t = modelPrimitive t t - modelPrimitive t 0 := h
    _ = 12 * Real.exp (t / 4) - 12 - 4 * t := by
      simp [modelPrimitive]
      ring

theorem modelWeightedError_pos (t : ℝ) (ht : 6 ≤ t) :
    0 < modelWeightedError t := by
  rw [modelWeightedError_eq]
  have he := Real.add_one_le_exp (t / 8)
  have he0 := Real.exp_pos (t / 8)
  have ht0 : 0 ≤ t / 8 + 1 := by linarith
  have hsquare : (t / 8 + 1) ^ 2 ≤ (Real.exp (t / 8)) ^ 2 := by
    nlinarith
  have hexp : Real.exp (t / 4) = (Real.exp (t / 8)) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [← hexp] at hsquare
  nlinarith [mul_nonneg (show 0 ≤ t by linarith) (show 0 < 3 * t - 16 by linarith).le]

/-- Weighted error for an arbitrary function expressed in logarithmic coordinates. -/
def weightedError (psi : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..t,
    (psi v - Real.exp v) * Real.exp (-v / 2) * (1 + (t - v) / 2)

private theorem lowerPrefix_integral (a t : ℝ) :
    (∫ v in (0 : ℝ)..a, -Real.exp (v / 2) * (1 + (t - v) / 2)) =
      Real.exp (a / 2) * (a - t - 4) + t + 4 := by
  have hderiv (v : ℝ) : HasDerivAt
      (fun x => Real.exp (x / 2) * (x - t - 4))
      (-Real.exp (v / 2) * (1 + (t - v) / 2)) v := by
    convert (((hasDerivAt_id v).div_const 2).exp.mul
      (((hasDerivAt_id v).sub_const t).sub_const 4)) using 1
    · funext x
      dsimp
    · dsimp
      ring
  have hint : IntervalIntegrable
      (fun v : ℝ => -Real.exp (v / 2) * (1 + (t - v) / 2))
      MeasureTheory.volume 0 a := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hderiv v) hint
  calc
    _ = Real.exp (a / 2) * (a - t - 4) - Real.exp (0 / 2) * (0 - t - 4) := h
    _ = _ := by simp; ring

private theorem lowerTail_integral (a t : ℝ) :
    (∫ v in a..t, Real.exp a * Real.exp (-v / 2) * (1 + (t - v) / 2)) =
      Real.exp (a / 2) * (t - a) := by
  have hderiv (v : ℝ) : HasDerivAt
      (fun x => Real.exp a * ((x - t) * Real.exp (-x / 2)))
      (Real.exp a * Real.exp (-v / 2) * (1 + (t - v) / 2)) v := by
    convert ((((hasDerivAt_id v).sub_const t).mul
      (((hasDerivAt_id v).neg.div_const 2).exp)).const_mul (Real.exp a)) using 1
    dsimp
    simp only [Pi.neg_apply, id_eq]
    ring
  have hint : IntervalIntegrable
      (fun v : ℝ => Real.exp a * Real.exp (-v / 2) * (1 + (t - v) / 2))
      MeasureTheory.volume a t := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hderiv v) hint
  have he : Real.exp a * Real.exp (-a / 2) = Real.exp (a / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = Real.exp a * ((t - t) * Real.exp (-t / 2)) -
        Real.exp a * ((a - t) * Real.exp (-a / 2)) := h
    _ = (Real.exp a * Real.exp (-a / 2)) * (t - a) := by ring
    _ = _ := by rw [he]

/-- A conditional comparison for arbitrary weighted-error inputs.
The hypotheses do not hold for the actual Chebyshev function by anything
proved here; they are suitable for artificial surplus countermodels. -/
theorem weightedError_lower_of_surplus (psi : ℝ → ℝ) (a t : ℝ)
    (ha : 0 ≤ a) (hat : a ≤ t)
    (hpsi0 : ∀ v ∈ Set.Icc 0 a, 0 ≤ psi v)
    (hpsia : ∀ v ∈ Set.Icc a t, Real.exp v + Real.exp a ≤ psi v)
    (hint0 : IntervalIntegrable
      (fun v : ℝ => (psi v - Real.exp v) * Real.exp (-v / 2) *
        (1 + (t - v) / 2)) MeasureTheory.volume 0 a)
    (hinta : IntervalIntegrable
      (fun v : ℝ => (psi v - Real.exp v) * Real.exp (-v / 2) *
        (1 + (t - v) / 2)) MeasureTheory.volume a t) :
    t + 4 - 4 * Real.exp (a / 2) ≤ weightedError psi t := by
  have hintLo0 : IntervalIntegrable
      (fun v : ℝ => -Real.exp (v / 2) * (1 + (t - v) / 2))
      MeasureTheory.volume 0 a := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hintLoa : IntervalIntegrable
      (fun v : ℝ => Real.exp a * Real.exp (-v / 2) * (1 + (t - v) / 2))
      MeasureTheory.volume a t := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hlo0 := intervalIntegral.integral_mono_on ha hintLo0 hint0
    (fun v hv => by
      have he : Real.exp v * Real.exp (-v / 2) = Real.exp (v / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hk : 0 ≤ 1 + (t - v) / 2 := by linarith [hv.2]
      have hp : -Real.exp v ≤ psi v - Real.exp v := by linarith [hpsi0 v hv]
      calc
        -Real.exp (v / 2) * (1 + (t - v) / 2) =
            (-Real.exp v) * Real.exp (-v / 2) * (1 + (t - v) / 2) := by rw [← he]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le) hk)
  have hloa := intervalIntegral.integral_mono_on hat hintLoa hinta
    (fun v hv => by
      have hk : 0 ≤ 1 + (t - v) / 2 := by linarith [hv.2]
      have hp : Real.exp a ≤ psi v - Real.exp v := by linarith [hpsia v hv]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le) hk)
  rw [lowerPrefix_integral] at hlo0
  rw [lowerTail_integral] at hloa
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hint0 hinta
  unfold weightedError
  linarith

#print axioms modelPsi_zero
#print axioms modelPsi_monotone
#print axioms modelPsi_nonneg
#print axioms modelPsi_sub_exp
#print axioms modelError_abs_le
#print axioms modelError_relative_abs_le
#print axioms modelError_pnt_envelope
#print axioms modelWeightedError_eq_convolution
#print axioms modelWeightedError_eq
#print axioms modelWeightedError_pos
#print axioms weightedError_lower_of_surplus

end RhCertificates.PrimeObstruction
