module

public import RhCertificates.SmoothSeries
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
The finite prime contribution vanishes through the first prime event.

The coefficient function is arbitrary. It may later be instantiated as the
von-Mangoldt weight divided by sqrt(n), but no identity with a published screw
function is silently assumed here.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace RhCertificates.PrimeStartup

def primeContribution (weight : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊, weight n * (t - Real.log (n : ℝ))

def fullExpression (C : ℝ) (weight : ℕ → ℝ) (t : ℝ) : ℝ :=
  SmoothSeries.smoothPart C t + primeContribution weight t

/-- Any finite set of permitted prime-event indices contributes zero when
the argument is at most log(2), including that endpoint. -/
theorem weighted_sum_zero_of_log_cutoff
    (s : Finset ℕ) (weight : ℕ → ℝ) (t : ℝ)
    (ht : t ≤ Real.log 2)
    (hs : ∀ n ∈ s, 2 ≤ n ∧ Real.log (n : ℝ) ≤ t) :
    (∑ n ∈ s, weight n * (t - Real.log (n : ℝ))) = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  obtain ⟨hn_lower, hn_log⟩ := hs n hn
  have hn_real : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_lower
  have hlog_lower : Real.log 2 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) hn_real
  have hzero : t - Real.log (n : ℝ) = 0 := by linarith
  rw [hzero, mul_zero]

theorem primeContribution_zero (weight : ℕ → ℝ) (t : ℝ)
    (ht : t ≤ Real.log 2) : primeContribution weight t = 0 := by
  unfold primeContribution
  apply weighted_sum_zero_of_log_cutoff _ weight t ht
  intro n hn
  obtain ⟨hn_lower, hn_upper⟩ := Finset.mem_Icc.mp hn
  refine ⟨hn_lower, ?_⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ)) hn_lower
    exact_mod_cast this
  have hn_exp : (n : ℝ) ≤ Real.exp t :=
    le_trans (by exact_mod_cast hn_upper) (Nat.floor_le (Real.exp_pos t).le)
  calc
    Real.log (n : ℝ) ≤ Real.log (Real.exp t) := Real.log_le_log hn_pos hn_exp
    _ = t := Real.log_exp t

theorem fullExpression_eq_smoothPart (C : ℝ) (weight : ℕ → ℝ) (t : ℝ)
    (ht : t ≤ Real.log 2) :
    fullExpression C weight t = SmoothSeries.smoothPart C t := by
  rw [fullExpression, primeContribution_zero weight t ht, add_zero]

/-- Transfer a separately proved smooth-part sign to the displayed full finite
formula on the startup interval. This theorem does not assert the smooth-part
sign as an unconditional premise-free result. -/
theorem fullExpression_negative_on_startup
    (C : ℝ) (weight : ℕ → ℝ)
    (hsmooth : ∀ t : ℝ, 0 < t → SmoothSeries.smoothPart C t < 0) :
    ∀ t : ℝ, 0 < t → t ≤ Real.log 2 → fullExpression C weight t < 0 := by
  intro t ht hcutoff
  rw [fullExpression_eq_smoothPart C weight t hcutoff]
  exact hsmooth t ht

#print axioms weighted_sum_zero_of_log_cutoff
#print axioms primeContribution_zero
#print axioms fullExpression_eq_smoothPart
#print axioms fullExpression_negative_on_startup

end RhCertificates.PrimeStartup
