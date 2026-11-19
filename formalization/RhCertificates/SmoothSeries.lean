module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
The displayed prime-free smooth part in ns_startup_lemma.md, using an arbitrary
linear coefficient C. The natural index n=0 denotes the k=1 term of that note.
No identity with the published screw function is assumed or established here.
-/

public section
noncomputable section

namespace RhCertificates.SmoothSeries

def coefficient (n : ℕ) : ℝ := 4 / (4 * ((n : ℝ) + 1) + 1) ^ 2

def rate (n : ℕ) : ℝ := 2 * ((n : ℝ) + 1) + 1 / 2

def term (n : ℕ) (t : ℝ) : ℝ :=
  coefficient n * (1 - Real.exp (-(rate n * t)))

def smoothPart (C t : ℝ) : ℝ :=
  -4 * (Real.exp (t / 2) - 1) + C * t - ∑' n : ℕ, term n t

theorem summable_dominator :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  apply (h.comp_injective Nat.succ_injective).congr
  intro n
  simp

theorem coefficient_nonneg (n : ℕ) : 0 ≤ coefficient n := by
  unfold coefficient
  positivity

theorem coefficient_le_dominator (n : ℕ) :
    coefficient n ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hden : 0 < (4 * ((n : ℝ) + 1) + 1) ^ 2 := by positivity
  have hdom : 0 < ((n : ℝ) + 1) ^ 2 := by positivity
  unfold coefficient
  apply (div_le_div_iff₀ hden hdom).mpr
  nlinarith

theorem term_nonneg (n : ℕ) (t : ℝ) (ht : 0 ≤ t) : 0 ≤ term n t := by
  have hr : 0 ≤ rate n := by unfold rate; positivity
  have he : Real.exp (-(rate n * t)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hr ht))
  exact mul_nonneg (coefficient_nonneg n) (sub_nonneg.mpr he)

theorem norm_term_le_dominator (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ‖term n t‖ ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (term_nonneg n t ht)]
  apply le_trans _ (coefficient_le_dominator n)
  unfold term
  have he : 0 ≤ Real.exp (-(rate n * t)) := (Real.exp_pos _).le
  nlinarith [coefficient_nonneg n,
    mul_nonneg (coefficient_nonneg n) he]

theorem summable_term (t : ℝ) (ht : 0 ≤ t) : Summable (fun n : ℕ => term n t) :=
  summable_dominator.of_norm_bounded (fun n => norm_term_le_dominator n t ht)

theorem continuousOn_smoothPart (C : ℝ) :
    ContinuousOn (smoothPart C) (Set.Ici 0) := by
  have hsum : ContinuousOn (fun t : ℝ => ∑' n : ℕ, term n t) (Set.Ici 0) := by
    apply continuousOn_tsum (u := fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2)
    · intro n
      have h : Continuous (term n) := by unfold term; fun_prop
      exact h.continuousOn
    · exact summable_dominator
    · intro n t ht
      exact norm_term_le_dominator n t ht
  have hfinite : Continuous (fun t : ℝ => -4 * (Real.exp (t / 2) - 1) + C * t) := by
    fun_prop
  exact hfinite.continuousOn.sub hsum

theorem smoothPart_zero (C : ℝ) : smoothPart C 0 = 0 := by
  simp [smoothPart, term]

/-- The coefficient is the k=n+1 coefficient in the displayed written series. -/
theorem coefficient_eq_written (n : ℕ) :
    coefficient n = 1 / (4 * ((n : ℝ) + 1 + 1 / 4) ^ 2) := by
  unfold coefficient
  have h1 : (4 : ℝ) * ((n : ℝ) + 1) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 1 + 1 / 4 ≠ 0 := by positivity
  field_simp

/-- Twice differentiating the exponential tail cancels its coefficient. -/
theorem coefficient_mul_rate_sq (n : ℕ) : coefficient n * (rate n) ^ 2 = 1 := by
  unfold coefficient rate
  have h : (4 : ℝ) * ((n : ℝ) + 1) + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem term_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (term n)
      (coefficient n * rate n * Real.exp (-(rate n * t))) t := by
  have he := (((hasDerivAt_id t).const_mul (rate n)).neg).exp
  convert ((hasDerivAt_const t 1).sub he).const_mul (coefficient n) using 1
  · funext x
    simp [term]
  · dsimp
    ring

theorem term_derivative_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => coefficient n * rate n * Real.exp (-(rate n * x)))
      (-Real.exp (-(rate n * t))) t := by
  have he := ((((hasDerivAt_id t).const_mul (rate n)).neg).exp).const_mul
    (coefficient n * rate n)
  convert he using 1
  · dsimp
  · simp only [Pi.neg_apply, id_eq, mul_one]
    have hc := coefficient_mul_rate_sq n
    nlinarith [congrArg (fun x : ℝ => x * Real.exp (-(rate n * t))) hc]

theorem exponential_tail_eq_geometric (n : ℕ) (t : ℝ) :
    Real.exp (-(rate n * t)) =
      Real.exp (-(5 * t / 2)) * (Real.exp (-(2 * t))) ^ n := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  unfold rate
  ring

theorem exponential_tail_summable (t : ℝ) (ht : 0 < t) :
    Summable (fun n : ℕ => Real.exp (-(rate n * t))) := by
  have hq : ‖Real.exp (-(2 * t))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  apply ((summable_geometric_of_norm_lt_one hq).mul_left
    (Real.exp (-(5 * t / 2)))).congr
  intro n
  exact (exponential_tail_eq_geometric n t).symm

theorem exponential_tail_tsum (t : ℝ) (ht : 0 < t) :
    (∑' n : ℕ, Real.exp (-(rate n * t))) =
      Real.exp (-t / 2) / (Real.exp (2 * t) - 1) := by
  have hq : ‖Real.exp (-(2 * t))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  rw [tsum_congr (fun n => exponential_tail_eq_geometric n t), tsum_mul_left,
    tsum_geometric_of_norm_lt_one hq]
  have hfactor : Real.exp (-(5 * t / 2)) =
      Real.exp (-t / 2) / Real.exp (2 * t) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [hfactor, Real.exp_neg]
  have he0 : Real.exp (2 * t) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have he1 : Real.exp (2 * t) - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by linarith)))
  field_simp

#print axioms summable_dominator
#print axioms coefficient_nonneg
#print axioms coefficient_le_dominator
#print axioms term_nonneg
#print axioms norm_term_le_dominator
#print axioms summable_term
#print axioms continuousOn_smoothPart
#print axioms smoothPart_zero
#print axioms coefficient_eq_written
#print axioms coefficient_mul_rate_sq
#print axioms term_hasDerivAt
#print axioms term_derivative_hasDerivAt
#print axioms exponential_tail_eq_geometric
#print axioms exponential_tail_summable
#print axioms exponential_tail_tsum

end RhCertificates.SmoothSeries
