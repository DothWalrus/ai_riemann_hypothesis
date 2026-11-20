module

public import RhCertificates.ArithmeticCancellation
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

/-!
Loss forced by nonnegative factorial-floor majorants. The actual von Mangoldt
weights are used in the finite weighted inequality. Applications to an
archimedean RH target require an explicit bounded-margin hypothesis; no RH
assumption or unproved analytic bridge is introduced here.
-/

public section
noncomputable section

open Finset Filter
open scoped Topology

namespace RhCertificates.MajorantLoss

open ArithmeticCancellation

def floorKernel (T : Finset ℕ) (a : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ m ∈ T, a m * ((m / d : ℕ) : ℝ)

def weightedCost (D : Finset ℕ) (K : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, ArithmeticFunction.vonMangoldt d * K d

def primeSum (D : Finset ℕ) (x : ℝ) : ℝ :=
  ∑ d ∈ D, ArithmeticFunction.vonMangoldt d * kernelWeight x d

def weightedExcess (D : Finset ℕ) (K : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ d ∈ D, ArithmeticFunction.vonMangoldt d * (K d - kernelWeight x d)

def delta (x : ℝ) : ℝ := 2 * kernelWeight x 4 - kernelWeight x 2

def minimumLoss (x : ℝ) : ℝ := Real.log 2 * delta x

def factorialCost (T : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ m ∈ T, a m * Real.log (m.factorial : ℝ)

theorem factorial_floor_identity (N : ℕ) :
    (∑ d ∈ Ioc 0 N, ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ)) =
      Real.log (N.factorial : ℝ) := by
  have h := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum
    (R := ℝ) ArithmeticFunction.vonMangoldt N
  simp only [ArithmeticFunction.vonMangoldt_mul_zeta, ArithmeticFunction.log_apply] at h
  rw [← h]
  exact Real.sum_log_eq_log_factorial N

theorem factorialCost_eq_weightedCost (N : ℕ) (T : Finset ℕ) (a : ℕ → ℝ)
    (hT : ∀ m ∈ T, m ≤ N) :
    factorialCost T a = weightedCost (Ioc 0 N) (floorKernel T a) := by
  unfold factorialCost weightedCost floorKernel
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro m hm
  have hsubset : Ioc 0 m ⊆ Ioc 0 N := Ioc_subset_Ioc le_rfl (hT m hm)
  have htrunc : (∑ d ∈ Ioc 0 N, ArithmeticFunction.vonMangoldt d * ((m / d : ℕ) : ℝ)) =
      Real.log (m.factorial : ℝ) := by
    calc
      _ = ∑ d ∈ Ioc 0 m, ArithmeticFunction.vonMangoldt d * ((m / d : ℕ) : ℝ) := by
        symm
        apply sum_subset hsubset
        intro d hd hdnot
        have hdm : m < d := by
          simp only [mem_Ioc] at hd hdnot
          omega
        simp [Nat.div_eq_of_lt hdm]
      _ = _ := factorial_floor_identity m
  rw [← htrunc, mul_sum]
  apply sum_congr rfl
  intro d _
  ring

/-- Without a support cutoff, extra nonnegative coefficients can only
increase the full factorial cost relative to a truncated prime-power sum. -/
theorem weightedCost_le_factorialCost (N : ℕ) (T : Finset ℕ) (a : ℕ → ℝ)
    (ha : ∀ m ∈ T, 0 ≤ a m) :
    weightedCost (Ioc 0 N) (floorKernel T a) ≤ factorialCost T a := by
  let M := N + T.sup id
  have hNM : N ≤ M := by dsimp [M]; omega
  have hT : ∀ m ∈ T, m ≤ M := by
    intro m hm
    have hsup : m ≤ T.sup id := by
      simpa only [id_eq] using (Finset.le_sup (f := id) hm)
    dsimp [M]
    omega
  rw [factorialCost_eq_weightedCost M T a hT]
  unfold weightedCost
  apply sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc le_rfl hNM)
  intro d _ _
  apply mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
  unfold floorKernel
  exact sum_nonneg (fun m hm => mul_nonneg (ha m hm) (Nat.cast_nonneg _))

theorem cost_sub_primeSum (D : Finset ℕ) (K : ℕ → ℝ) (x : ℝ) :
    weightedCost D K - primeSum D x = weightedExcess D K x := by
  simp only [weightedCost, primeSum, weightedExcess, mul_sub, sum_sub_distrib]

theorem excess_two_ge_delta (T : Finset ℕ) (a : ℕ → ℝ) (x : ℝ)
    (ha : ∀ m ∈ T, 0 ≤ a m)
    (h4 : kernelWeight x 4 ≤ floorKernel T a 4) :
    delta x ≤ floorKernel T a 2 - kernelWeight x 2 := by
  have h := binary_weight_necessary T a ha
  change 2 * floorKernel T a 4 ≤ floorKernel T a 2 at h
  unfold delta
  linarith

theorem weightedExcess_ge_minimumLoss (D T : Finset ℕ) (a : ℕ → ℝ) (x : ℝ)
    (h2D : 2 ∈ D) (h4D : 4 ∈ D) (ha : ∀ m ∈ T, 0 ≤ a m)
    (hmajor : ∀ d ∈ D, IsPrimePow d → kernelWeight x d ≤ floorKernel T a d) :
    minimumLoss x ≤ weightedExcess D (floorKernel T a) x := by
  have h4 : IsPrimePow (4 : ℕ) := by
    exact ⟨2, 2, Nat.prime_two.prime, by norm_num, by norm_num⟩
  have hexcess := excess_two_ge_delta T a x ha (hmajor 4 h4D h4)
  have hlog : 0 ≤ Real.log (2 : ℝ) := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hnonneg : ∀ d ∈ D,
      0 ≤ ArithmeticFunction.vonMangoldt d * (floorKernel T a d - kernelWeight x d) := by
    intro d hd
    by_cases hp : IsPrimePow d
    · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (sub_nonneg.mpr (hmajor d hd hp))
    · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hp]
      simp
  have hsingle := single_le_sum hnonneg h2D
  have hLambda : ArithmeticFunction.vonMangoldt 2 = Real.log 2 :=
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
  calc
    minimumLoss x ≤ ArithmeticFunction.vonMangoldt 2 * (floorKernel T a 2 - kernelWeight x 2) := by
      unfold minimumLoss
      rw [hLambda]
      exact mul_le_mul_of_nonneg_left hexcess hlog
    _ ≤ _ := hsingle

theorem weightedCost_sub_primeSum_ge_minimumLoss
    (D T : Finset ℕ) (a : ℕ → ℝ) (x : ℝ)
    (h2D : 2 ∈ D) (h4D : 4 ∈ D) (ha : ∀ m ∈ T, 0 ≤ a m)
    (hmajor : ∀ d ∈ D, IsPrimePow d → kernelWeight x d ≤ floorKernel T a d) :
    minimumLoss x ≤ weightedCost D (floorKernel T a) - primeSum D x := by
  rw [cost_sub_primeSum]
  exact weightedExcess_ge_minimumLoss D T a x h2D h4D ha hmajor

theorem factorialCost_sub_primeSum_ge_minimumLoss (N : ℕ) (hN : 4 ≤ N)
    (T : Finset ℕ) (a : ℕ → ℝ) (x : ℝ)
    (hT : ∀ m ∈ T, m ≤ N) (ha : ∀ m ∈ T, 0 ≤ a m)
    (hmajor : ∀ d ∈ Ioc 0 N, IsPrimePow d → kernelWeight x d ≤ floorKernel T a d) :
    minimumLoss x ≤ factorialCost T a - primeSum (Ioc 0 N) x := by
  rw [factorialCost_eq_weightedCost N T a hT]
  apply weightedCost_sub_primeSum_ge_minimumLoss (Ioc 0 N) T a x
    (by simp; omega) (by simp; omega) ha hmajor

theorem factorialCost_sub_primeSum_ge_minimumLoss_unrestricted (N : ℕ) (hN : 4 ≤ N)
    (T : Finset ℕ) (a : ℕ → ℝ) (x : ℝ) (ha : ∀ m ∈ T, 0 ≤ a m)
    (hmajor : ∀ d ∈ Ioc 0 N, IsPrimePow d → kernelWeight x d ≤ floorKernel T a d) :
    minimumLoss x ≤ factorialCost T a - primeSum (Ioc 0 N) x := by
  have hcost := weightedCost_le_factorialCost N T a ha
  have hloss := weightedCost_sub_primeSum_ge_minimumLoss (Ioc 0 N) T a x
    (by simp; omega) (by simp; omega) ha hmajor
  linarith

theorem delta_affine (x : ℝ) (hx : 0 < x) :
    delta x = (1 - 1 / Real.sqrt 2) * Real.log x +
      (1 / Real.sqrt 2 - 2) * Real.log 2 := by
  have h := binary_kernel_difference x hx
  unfold delta
  linarith

theorem minimumLoss_pos (x : ℝ) (hx : 32 ≤ x) : 0 < minimumLoss x := by
  apply mul_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  unfold delta
  linarith [binary_actual_weight_violation_of_large x hx]

theorem loss_coefficient_pos : 0 < Real.log 2 * (1 - 1 / Real.sqrt 2) := by
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs1 : 1 < Real.sqrt (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hdiv : 1 / Real.sqrt (2 : ℝ) < 1 := (div_lt_one hs).mpr hs1
  exact mul_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2)) (sub_pos.mpr hdiv)

theorem minimumLoss_tendsto_atTop : Tendsto minimumLoss atTop atTop := by
  have hlin : Tendsto (fun x : ℝ =>
      (Real.log 2 * (1 - 1 / Real.sqrt 2)) * Real.log x +
      Real.log 2 * ((1 / Real.sqrt 2 - 2) * Real.log 2)) atTop atTop :=
    tendsto_atTop_add_const_right atTop _
      (Filter.Tendsto.const_mul_atTop loss_coefficient_pos Real.tendsto_log_atTop)
  apply hlin.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold minimumLoss
  rw [delta_affine x hx]
  ring

/-- Conditional barrier for direct comparisons with a bounded permissible
margin. No assertion about the actual RH archimedean margin is made here. -/
theorem eventual_failure_of_bounded_margin (P S A : ℝ → ℝ) (B : ℝ)
    (hloss : ∀ᶠ x : ℝ in atTop, minimumLoss x ≤ P x - S x)
    (hmargin : ∀ᶠ x : ℝ in atTop, A x - S x ≤ B) :
    ∀ᶠ x : ℝ in atTop, A x < P x := by
  have hlarge : ∀ᶠ x : ℝ in atTop, B < minimumLoss x :=
    minimumLoss_tendsto_atTop.eventually (eventually_gt_atTop B)
  filter_upwards [hlarge, hloss, hmargin] with x hx hl hm
  linarith

/-- Direct factorial majorants fail eventually if the permissible margin
over the true prime sum is bounded. All coefficient/support/majorization
conditions are supplied explicitly; the bounded margin is not derived here. -/
theorem factorial_majorants_fail_with_bounded_margin
    (N : ℝ → ℕ) (T : ℝ → Finset ℕ) (a : ℝ → ℕ → ℝ) (A : ℝ → ℝ) (B : ℝ)
    (hN : ∀ᶠ x : ℝ in atTop, 4 ≤ N x)
    (hT : ∀ᶠ x : ℝ in atTop, ∀ m ∈ T x, m ≤ N x)
    (ha : ∀ᶠ x : ℝ in atTop, ∀ m ∈ T x, 0 ≤ a x m)
    (hmajor : ∀ᶠ x : ℝ in atTop, ∀ d ∈ Ioc 0 (N x),
      IsPrimePow d → kernelWeight x d ≤ floorKernel (T x) (a x) d)
    (hmargin : ∀ᶠ x : ℝ in atTop, A x - primeSum (Ioc 0 (N x)) x ≤ B) :
    ∀ᶠ x : ℝ in atTop, A x < factorialCost (T x) (a x) := by
  apply eventual_failure_of_bounded_margin
    (fun x => factorialCost (T x) (a x)) (fun x => primeSum (Ioc 0 (N x)) x) A B
  · filter_upwards [hN, hT, ha, hmajor] with x hNx hTx hax hmx
    exact factorialCost_sub_primeSum_ge_minimumLoss (N x) hNx (T x) (a x) x hTx hax hmx
  · exact hmargin

theorem positive_factorial_majorants_fail
    (N : ℝ → ℕ) (T : ℝ → Finset ℕ) (a : ℝ → ℕ → ℝ) (A : ℝ → ℝ) (B : ℝ)
    (hN : ∀ᶠ x : ℝ in atTop, 4 ≤ N x)
    (ha : ∀ᶠ x : ℝ in atTop, ∀ m ∈ T x, 0 ≤ a x m)
    (hmajor : ∀ᶠ x : ℝ in atTop, ∀ d ∈ Ioc 0 (N x),
      IsPrimePow d → kernelWeight x d ≤ floorKernel (T x) (a x) d)
    (hmargin : ∀ᶠ x : ℝ in atTop, A x - primeSum (Ioc 0 (N x)) x ≤ B) :
    ∀ᶠ x : ℝ in atTop, A x < factorialCost (T x) (a x) := by
  apply eventual_failure_of_bounded_margin
    (fun x => factorialCost (T x) (a x)) (fun x => primeSum (Ioc 0 (N x)) x) A B
  · filter_upwards [hN, ha, hmajor] with x hNx hax hmx
    exact factorialCost_sub_primeSum_ge_minimumLoss_unrestricted
      (N x) hNx (T x) (a x) x hax hmx
  · exact hmargin

#print axioms cost_sub_primeSum
#print axioms factorial_floor_identity
#print axioms factorialCost_eq_weightedCost
#print axioms weightedCost_le_factorialCost
#print axioms excess_two_ge_delta
#print axioms weightedExcess_ge_minimumLoss
#print axioms weightedCost_sub_primeSum_ge_minimumLoss
#print axioms factorialCost_sub_primeSum_ge_minimumLoss
#print axioms factorialCost_sub_primeSum_ge_minimumLoss_unrestricted
#print axioms delta_affine
#print axioms minimumLoss_pos
#print axioms loss_coefficient_pos
#print axioms minimumLoss_tendsto_atTop
#print axioms eventual_failure_of_bounded_margin
#print axioms factorial_majorants_fail_with_bounded_margin
#print axioms positive_factorial_majorants_fail

end RhCertificates.MajorantLoss
