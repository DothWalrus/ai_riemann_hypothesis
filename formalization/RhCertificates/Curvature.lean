module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

/-!
Exact curvature algebra for the smooth startup function. These statements
do not establish that the actual function has this second derivative.
-/

public section

namespace RhCertificates

/-- The cubic controlling curvature is strictly increasing for y >= 1. -/
theorem curvature_cubic_strictMonoOn :
    StrictMonoOn (fun y : ℝ => y ^ 3 - y - 1) (Set.Ici 1) := by
  intro x hx y hy hxy
  have hx1 : 1 ≤ x := hx
  have hy1 : 1 ≤ y := hy
  have hx_sq : (1 : ℝ) ≤ x ^ 2 := by nlinarith [sq_nonneg (x - 1)]
  have hy_sq : (1 : ℝ) ≤ y ^ 2 := by nlinarith [sq_nonneg (y - 1)]
  have hprod_nonneg : 0 ≤ y * x := mul_nonneg (by linarith) (by linarith)
  have hfactor : 0 < y ^ 2 + y * x + x ^ 2 - 1 := by linarith
  have hprod := mul_pos (sub_pos.mpr hxy) hfactor
  dsimp
  nlinarith

/-- Rational form of the curvature after setting r = exp(t/2), y = exp(t). -/
theorem curvature_rational_identity (r y : ℝ)
    (hr : 0 < r) (hy : 1 < y) (hsq : r ^ 2 = y) :
    -r + (1 / r) / (y ^ 2 - 1) =
      -(y ^ 3 - y - 1) / (r * (y ^ 2 - 1)) := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hden : y ^ 2 - 1 ≠ 0 := by nlinarith
  field_simp
  nlinarith [congrArg (fun z : ℝ => z * (y ^ 2 - 1)) hsq]

/-- The curvature has the opposite sign of the cubic on the positive domain. -/
theorem curvature_nonpos_iff_cubic_nonneg (r y : ℝ)
    (hr : 0 < r) (hy : 1 < y) (hsq : r ^ 2 = y) :
    (-r + (1 / r) / (y ^ 2 - 1) ≤ 0) ↔ 0 ≤ y ^ 3 - y - 1 := by
  rw [curvature_rational_identity r y hr hy hsq]
  have hden : 0 < r * (y ^ 2 - 1) := mul_pos hr (by nlinarith)
  rw [div_le_iff₀ hden]
  constructor <;> intro h <;> nlinarith

#print axioms curvature_cubic_strictMonoOn
#print axioms curvature_rational_identity
#print axioms curvature_nonpos_iff_cubic_nonneg

/-- The actual exponential expression has the cubic's opposite sign. -/
theorem exponential_curvature_nonpos_iff (t : ℝ) (ht : 0 < t) :
    (-Real.exp (t / 2) + Real.exp (-t / 2) / (Real.exp (2 * t) - 1) ≤ 0) ↔
      0 ≤ (Real.exp t) ^ 3 - Real.exp t - 1 := by
  have hsq : (Real.exp (t / 2)) ^ 2 = Real.exp t := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hdouble : Real.exp (2 * t) = (Real.exp t) ^ 2 := Real.exp_nat_mul t 2
  have hnegative : Real.exp (-t / 2) = 1 / Real.exp (t / 2) := by
    rw [show -t / 2 = -(t / 2) by ring, Real.exp_neg, one_div]
  rw [hdouble, hnegative]
  exact curvature_nonpos_iff_cubic_nonneg _ _ (Real.exp_pos _)
    (Real.one_lt_exp_iff.mpr ht) hsq

/-- An exact Taylor bound places exp(1/4) below 13/10, without Python data. -/
theorem exp_quarter_lt_thirteen_tenths : Real.exp ((1 : ℝ) / 4) < 13 / 10 := by
  have h := Real.exp_bound' (x := (1 : ℝ) / 4) (by norm_num) (by norm_num)
    (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

/-- The curvature cubic is negative at exp(1/4) and positive at exp(1/3). -/
theorem curvature_cubic_exp_bracket :
    (Real.exp ((1 : ℝ) / 4)) ^ 3 - Real.exp ((1 : ℝ) / 4) - 1 < 0 ∧
      0 < (Real.exp ((1 : ℝ) / 3)) ^ 3 - Real.exp ((1 : ℝ) / 3) - 1 := by
  constructor
  · have h := curvature_cubic_strictMonoOn
      (show Real.exp ((1 : ℝ) / 4) ∈ Set.Ici 1 from
        le_of_lt (Real.one_lt_exp_iff.mpr (by norm_num)))
      (show (13 / 10 : ℝ) ∈ Set.Ici 1 by norm_num)
      exp_quarter_lt_thirteen_tenths
    norm_num at h
    linarith
  · have hlower : (4 / 3 : ℝ) ≤ Real.exp ((1 : ℝ) / 3) := by
      have h := Real.add_one_le_exp ((1 : ℝ) / 3)
      linarith
    have h := curvature_cubic_strictMonoOn.monotoneOn
      (show (4 / 3 : ℝ) ∈ Set.Ici 1 by norm_num)
      (show Real.exp ((1 : ℝ) / 3) ∈ Set.Ici 1 from
        (show 1 ≤ Real.exp ((1 : ℝ) / 3) by linarith))
      hlower
    norm_num at h
    linarith

#print axioms exponential_curvature_nonpos_iff
#print axioms exp_quarter_lt_thirteen_tenths
#print axioms curvature_cubic_exp_bracket

/-- Sign counterpart needed on the convex initial interval. -/
theorem exponential_curvature_nonneg_iff (t : ℝ) (ht : 0 < t) :
    (0 ≤ -Real.exp (t / 2) + Real.exp (-t / 2) / (Real.exp (2 * t) - 1)) ↔
      (Real.exp t) ^ 3 - Real.exp t - 1 ≤ 0 := by
  have hsq : (Real.exp (t / 2)) ^ 2 = Real.exp t := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hdouble : Real.exp (2 * t) = (Real.exp t) ^ 2 := Real.exp_nat_mul t 2
  have hnegative : Real.exp (-t / 2) = 1 / Real.exp (t / 2) := by
    rw [show -t / 2 = -(t / 2) by ring, Real.exp_neg, one_div]
  rw [hdouble, hnegative, curvature_rational_identity _ _ (Real.exp_pos _)
    (Real.one_lt_exp_iff.mpr ht) hsq]
  have hy : 1 < Real.exp t := Real.one_lt_exp_iff.mpr ht
  have hden : 0 < Real.exp (t / 2) * ((Real.exp t) ^ 2 - 1) :=
    mul_pos (Real.exp_pos _) (by nlinarith)
  rw [le_div_iff₀ hden]
  constructor <;> intro h <;> nlinarith

/-- There is a transition strictly between 1/4 and 1/3, and the displayed
curvature is nonnegative before it and nonpositive after it. -/
theorem exists_exponential_curvature_transition :
    ∃ a : ℝ, (1 : ℝ) / 4 < a ∧ a < (1 : ℝ) / 3 ∧
      (∀ t : ℝ, 0 < t → t ≤ a →
        0 ≤ -Real.exp (t / 2) + Real.exp (-t / 2) / (Real.exp (2 * t) - 1)) ∧
      (∀ t : ℝ, a ≤ t →
        -Real.exp (t / 2) + Real.exp (-t / 2) / (Real.exp (2 * t) - 1) ≤ 0) := by
  let P : ℝ → ℝ := fun t => (Real.exp t) ^ 3 - Real.exp t - 1
  have hcont : ContinuousOn P (Set.Icc ((1 : ℝ) / 4) ((1 : ℝ) / 3)) := by
    dsimp [P]
    fun_prop
  have hbr := curvature_cubic_exp_bracket
  obtain ⟨a, ha, hazero⟩ := intermediate_value_Icc
    (show (1 : ℝ) / 4 ≤ (1 : ℝ) / 3 by norm_num) hcont
    (show (0 : ℝ) ∈ Set.Icc (P ((1 : ℝ) / 4)) (P ((1 : ℝ) / 3)) from
      ⟨le_of_lt hbr.1, le_of_lt hbr.2⟩)
  have hal : (1 : ℝ) / 4 < a := by
    rcases lt_or_eq_of_le ha.1 with h | h
    · exact h
    · rw [← h] at hazero
      dsimp [P] at hazero
      linarith [hbr.1]
  have hau : a < (1 : ℝ) / 3 := by
    rcases lt_or_eq_of_le ha.2 with h | h
    · exact h
    · rw [h] at hazero
      dsimp [P] at hazero
      linarith [hbr.2]
  have ha0 : 0 < a := by linarith
  have hea : Real.exp a ∈ Set.Ici 1 := le_of_lt (Real.one_lt_exp_iff.mpr ha0)
  refine ⟨a, hal, hau, ?_, ?_⟩
  · intro t ht hta
    apply (exponential_curvature_nonneg_iff t ht).mpr
    have het : Real.exp t ∈ Set.Ici 1 := le_of_lt (Real.one_lt_exp_iff.mpr ht)
    have h := curvature_cubic_strictMonoOn.monotoneOn het hea (Real.exp_le_exp.mpr hta)
    change P t ≤ P a at h
    rw [hazero] at h
    exact h
  · intro t hat
    have ht : 0 < t := lt_of_lt_of_le ha0 hat
    apply (exponential_curvature_nonpos_iff t ht).mpr
    have het : Real.exp t ∈ Set.Ici 1 := le_of_lt (Real.one_lt_exp_iff.mpr ht)
    have h := curvature_cubic_strictMonoOn.monotoneOn hea het (Real.exp_le_exp.mpr hat)
    change P a ≤ P t at h
    rw [hazero] at h
    exact h

#print axioms exponential_curvature_nonneg_iff
#print axioms exists_exponential_curvature_transition

end RhCertificates
