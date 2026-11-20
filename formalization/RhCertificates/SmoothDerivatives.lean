module

public import RhCertificates.SmoothSeries
public import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Locally uniform exponential majorants justify differentiating the displayed
smooth-part series twice on the positive half-line. This proves analytic
properties of the explicitly defined series, with arbitrary linear constant C.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped Topology

namespace RhCertificates.SmoothSeries

def derivativeTerm (n : ℕ) (t : ℝ) : ℝ :=
  coefficient n * rate n * Real.exp (-(rate n * t))

def smoothDerivative (C t : ℝ) : ℝ :=
  -2 * Real.exp (t / 2) + C - ∑' n : ℕ, derivativeTerm n t

theorem derivativeTerm_eq (n : ℕ) (t : ℝ) :
    derivativeTerm n t = coefficient n * rate n * Real.exp (-(rate n * t)) := rfl

theorem smoothDerivative_eq (C t : ℝ) :
    smoothDerivative C t = -2 * Real.exp (t / 2) + C -
      ∑' n : ℕ, derivativeTerm n t := rfl

theorem rate_ge_one (n : ℕ) : (1 : ℝ) ≤ rate n := by
  rw [rate_eq]
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

theorem coefficient_mul_rate_bounds (n : ℕ) :
    0 ≤ coefficient n * rate n ∧ coefficient n * rate n ≤ 1 := by
  have hrate : 0 ≤ rate n := le_trans (by norm_num) (rate_ge_one n)
  have hnonneg := mul_nonneg (coefficient_nonneg n) hrate
  refine ⟨hnonneg, ?_⟩
  have h := mul_le_mul_of_nonneg_left (rate_ge_one n) hnonneg
  nlinarith [coefficient_mul_rate_sq n]

/-- A uniform majorant for the derivative on every half-line t>=a>0. -/
theorem norm_derivativeTerm_le_exponential (n : ℕ) (a t : ℝ) (hat : a ≤ t) :
    ‖derivativeTerm n t‖ ≤ Real.exp (-(rate n * a)) := by
  have hb := coefficient_mul_rate_bounds n
  have hrate : 0 ≤ rate n := le_trans (by norm_num) (rate_ge_one n)
  have he : Real.exp (-(rate n * t)) ≤ Real.exp (-(rate n * a)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hat hrate]
  rw [derivativeTerm, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hb.1 (Real.exp_pos _).le)]
  exact le_trans (by nlinarith [Real.exp_pos (-(rate n * t))]) he

theorem derivativeTerm_summable (t : ℝ) (ht : 0 < t) :
    Summable (fun n : ℕ => derivativeTerm n t) :=
  (exponential_tail_summable t ht).of_norm_bounded
    (fun n => norm_derivativeTerm_le_exponential n t t le_rfl)

theorem term_tsum_hasDerivAt (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => ∑' n : ℕ, term n x)
      (∑' n : ℕ, derivativeTerm n t) t := by
  have hhalf : 0 < t / 2 := by linarith
  have hmem : t ∈ Ioi (t / 2) := by change t / 2 < t; linarith
  apply hasDerivAt_tsum_of_isPreconnected
    (g := term) (g' := derivativeTerm)
    (u := fun n : ℕ => Real.exp (-(rate n * (t / 2))))
    (t := Ioi (t / 2)) (y₀ := t)
    (exponential_tail_summable _ hhalf) isOpen_Ioi isPreconnected_Ioi
    (fun n x _ => term_hasDerivAt n x)
    (fun n x hx => norm_derivativeTerm_le_exponential n _ _ (le_of_lt hx))
    hmem (summable_term t (le_of_lt ht)) hmem

theorem derivativeTerm_tsum_hasDerivAt (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => ∑' n : ℕ, derivativeTerm n x)
      (-(∑' n : ℕ, Real.exp (-(rate n * t)))) t := by
  have hhalf : 0 < t / 2 := by linarith
  have hmem : t ∈ Ioi (t / 2) := by change t / 2 < t; linarith
  have h := hasDerivAt_tsum_of_isPreconnected
    (g := derivativeTerm) (g' := fun n x => -Real.exp (-(rate n * x)))
    (u := fun n : ℕ => Real.exp (-(rate n * (t / 2))))
    (t := Ioi (t / 2)) (y₀ := t)
    (exponential_tail_summable _ hhalf) isOpen_Ioi isPreconnected_Ioi
    (fun n x _ => term_derivative_hasDerivAt n x)
    (fun n x hx => ?_) hmem (derivativeTerm_summable t ht) hmem
  · simpa only [tsum_neg] using h
  · rw [norm_neg, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hrate : 0 ≤ rate n := le_trans (by norm_num) (rate_ge_one n)
    nlinarith [mul_le_mul_of_nonneg_left (le_of_lt hx) hrate]

theorem smoothPart_hasDerivAt (C t : ℝ) (ht : 0 < t) :
    HasDerivAt (smoothPart C) (smoothDerivative C t) t := by
  have he := (((hasDerivAt_id t).div_const 2).exp.sub_const 1).const_mul (-4)
  have hlinear := (hasDerivAt_id t).const_mul C
  convert (he.add hlinear).sub (term_tsum_hasDerivAt t ht) using 1
  · funext x
    rw [smoothPart_eq]
    rfl
  · dsimp [smoothDerivative]
    ring

theorem smoothPart_deriv (C t : ℝ) (ht : 0 < t) :
    deriv (smoothPart C) t = smoothDerivative C t :=
  (smoothPart_hasDerivAt C t ht).deriv

theorem smoothDerivative_hasDerivAt (C t : ℝ) (ht : 0 < t) :
    HasDerivAt (smoothDerivative C)
      (-Real.exp (t / 2) + Real.exp (-t / 2) / (Real.exp (2 * t) - 1)) t := by
  have he := ((((hasDerivAt_id t).div_const 2).exp).const_mul (-2)).add_const C
  have hs := derivativeTerm_tsum_hasDerivAt t ht
  convert he.sub hs using 1
  · funext x
    rfl
  · dsimp
    rw [exponential_tail_tsum t ht]
    ring

theorem smoothPart_deriv_hasDerivAt (C t : ℝ) (ht : 0 < t) :
    HasDerivAt (deriv (smoothPart C))
      (-Real.exp (t / 2) + Real.exp (-t / 2) / (Real.exp (2 * t) - 1)) t := by
  apply (smoothDerivative_hasDerivAt C t ht).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with x hx
  exact smoothPart_deriv C x hx

theorem smoothPart_second_deriv (C t : ℝ) (ht : 0 < t) :
    deriv (deriv (smoothPart C)) t =
      -Real.exp (t / 2) + Real.exp (-t / 2) / (Real.exp (2 * t) - 1) :=
  (smoothPart_deriv_hasDerivAt C t ht).deriv

theorem differentiableOn_smoothPart (C : ℝ) :
    DifferentiableOn ℝ (smoothPart C) (Ioi 0) := by
  intro t ht
  exact (smoothPart_hasDerivAt C t ht).differentiableAt.differentiableWithinAt

theorem differentiableOn_smoothPart_deriv (C : ℝ) :
    DifferentiableOn ℝ (deriv (smoothPart C)) (Ioi 0) := by
  intro t ht
  exact (smoothPart_deriv_hasDerivAt C t ht).differentiableAt.differentiableWithinAt

#print axioms derivativeTerm_eq
#print axioms smoothDerivative_eq
#print axioms rate_ge_one
#print axioms coefficient_mul_rate_bounds
#print axioms norm_derivativeTerm_le_exponential
#print axioms derivativeTerm_summable
#print axioms term_tsum_hasDerivAt
#print axioms derivativeTerm_tsum_hasDerivAt
#print axioms smoothPart_hasDerivAt
#print axioms smoothPart_deriv
#print axioms smoothDerivative_hasDerivAt
#print axioms smoothPart_deriv_hasDerivAt
#print axioms smoothPart_second_deriv
#print axioms differentiableOn_smoothPart
#print axioms differentiableOn_smoothPart_deriv

end RhCertificates.SmoothSeries
