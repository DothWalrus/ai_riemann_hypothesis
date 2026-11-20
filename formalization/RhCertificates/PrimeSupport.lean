module

public import RhCertificates.PrimeObstruction
public import Mathlib.Data.Nat.Find
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

/-!
Artificial weighted-event staircases. The event sequence is abstract; no
identification with prime powers or with the von Mangoldt weights is assumed.
-/

public section
noncomputable section

open Filter Set
open scoped Topology

namespace RhCertificates.PrimeSupport

def nextIndex (q : ℕ → ℝ) (hunbounded : ∀ x : ℝ, ∃ n, x < q n) (x : ℝ) : ℕ := by
  classical
  exact Nat.find (hunbounded x)

def nextEvent (q : ℕ → ℝ) (hunbounded : ∀ x : ℝ, ∃ n, x < q n) (x : ℝ) : ℝ :=
  q (nextIndex q hunbounded x)

def staircase (q : ℕ → ℝ) (hunbounded : ∀ x : ℝ, ∃ n, x < q n) (x : ℝ) : ℝ :=
  if x < q 0 then 0 else nextEvent q hunbounded x + q 0

theorem lt_nextEvent (q : ℕ → ℝ) (hunbounded : ∀ x : ℝ, ∃ n, x < q n) (x : ℝ) :
    x < nextEvent q hunbounded x := by
  classical
  exact Nat.find_spec (hunbounded x)

theorem nextIndex_monotone (q : ℕ → ℝ) (hunbounded : ∀ x : ℝ, ∃ n, x < q n) :
    Monotone (nextIndex q hunbounded) := by
  classical
  intro x y hxy
  exact Nat.find_min' (hunbounded x) (lt_of_le_of_lt hxy (lt_nextEvent q hunbounded y))

theorem nextEvent_monotone (q : ℕ → ℝ) (hunbounded : ∀ x : ℝ, ∃ n, x < q n)
    (hq : Monotone q) : Monotone (nextEvent q hunbounded) :=
  hq.comp (nextIndex_monotone q hunbounded)

theorem nextEvent_eq_on_gap (q : ℕ → ℝ) (hunbounded : ∀ x : ℝ, ∃ n, x < q n)
    (hq : StrictMono q) (n : ℕ) (x : ℝ) (hlo : q n ≤ x) (hhi : x < q (n + 1)) :
    nextEvent q hunbounded x = q (n + 1) := by
  classical
  have hle : nextIndex q hunbounded x ≤ n + 1 := Nat.find_min' (hunbounded x) hhi
  have hgt : n < nextIndex q hunbounded x := by
    by_contra! h
    have hqle := hq.monotone h
    have hx := lt_nextEvent q hunbounded x
    unfold nextEvent at hx
    linarith
  have hindex : nextIndex q hunbounded x = n + 1 := by omega
  simp only [nextEvent, hindex]

theorem event_indices_below_finite (q : ℕ → ℝ)
    (hunbounded : ∀ x : ℝ, ∃ n, x < q n) (hq : StrictMono q) (x : ℝ) :
    Set.Finite {n : ℕ | q n ≤ x} := by
  apply (Set.finite_Iio (nextIndex q hunbounded x)).subset
  intro n hn
  change n < nextIndex q hunbounded x
  by_contra! h
  have hqle := hq.monotone h
  have hx := lt_nextEvent q hunbounded x
  unfold nextEvent at hx
  exact (not_le_of_gt hx) (le_trans hqle hn)

theorem event_gaps_cover (q : ℕ → ℝ)
    (hunbounded : ∀ x : ℝ, ∃ n, x < q n) (x : ℝ) (hx : q 0 ≤ x) :
    ∃ n : ℕ, x ∈ Ico (q n) (q (n + 1)) := by
  classical
  have hpos : 0 < nextIndex q hunbounded x := by
    by_contra! h
    have hz : nextIndex q hunbounded x = 0 := Nat.eq_zero_of_le_zero h
    have hn := lt_nextEvent q hunbounded x
    simp only [nextEvent, hz] at hn
    linarith
  refine ⟨nextIndex q hunbounded x - 1, ?_, ?_⟩
  · apply le_of_not_gt
    apply Nat.find_min (hunbounded x)
    change nextIndex q hunbounded x - 1 < nextIndex q hunbounded x
    omega
  · have hn := lt_nextEvent q hunbounded x
    have heq : nextIndex q hunbounded x - 1 + 1 = nextIndex q hunbounded x := by omega
    simpa only [heq, nextEvent] using hn

theorem staircase_normalized (q : ℕ → ℝ) (hunbounded : ∀ x : ℝ, ∃ n, x < q n)
    (hq0 : 1 < q 0) : staircase q hunbounded 1 = 0 := by
  simp [staircase, hq0]

theorem staircase_nonneg (q : ℕ → ℝ) (hunbounded : ∀ x : ℝ, ∃ n, x < q n)
    (hq0 : 0 ≤ q 0) (x : ℝ) : 0 ≤ staircase q hunbounded x := by
  unfold staircase
  split_ifs with hx
  · exact le_rfl
  · have hn := lt_nextEvent q hunbounded x
    have hqx : q 0 ≤ x := le_of_not_gt hx
    linarith

theorem staircase_monotone (q : ℕ → ℝ) (hunbounded : ∀ x : ℝ, ∃ n, x < q n)
    (hq : Monotone q) (hq0 : 0 ≤ q 0) : Monotone (staircase q hunbounded) := by
  intro x y hxy
  by_cases hx : x < q 0
  · simp only [staircase, ite_eq_left hx]
    exact staircase_nonneg q hunbounded hq0 y
  · have hy : ¬ y < q 0 := by linarith
    simp only [staircase, ite_eq_right hx, ite_eq_right hy]
    linarith [nextEvent_monotone q hunbounded hq hxy]

theorem staircase_on_event_gap (q : ℕ → ℝ) (hunbounded : ∀ x : ℝ, ∃ n, x < q n)
    (hq : StrictMono q) (n : ℕ) (x : ℝ) (hx : x ∈ Ico (q n) (q (n + 1))) :
    staircase q hunbounded x = q (n + 1) + q 0 := by
  have hbase : q 0 ≤ x := le_trans (hq.monotone (Nat.zero_le n)) hx.1
  simp only [staircase, ite_eq_right (not_lt.mpr hbase)]
  rw [nextEvent_eq_on_gap q hunbounded hq n x hx.1 hx.2]

theorem staircase_event_value (q : ℕ → ℝ) (hunbounded : ∀ x : ℝ, ∃ n, x < q n)
    (hq : StrictMono q) (n : ℕ) :
    staircase q hunbounded (q n) = q (n + 1) + q 0 :=
  staircase_on_event_gap q hunbounded hq n (q n) ⟨le_rfl, hq (Nat.lt_succ_self n)⟩

theorem staircase_positive_event_increment (q : ℕ → ℝ)
    (hunbounded : ∀ x : ℝ, ∃ n, x < q n) (hq : StrictMono q) (n : ℕ) :
    0 < staircase q hunbounded (q (n + 1)) - staircase q hunbounded (q n) := by
  rw [staircase_event_value q hunbounded hq (n + 1), staircase_event_value q hunbounded hq n]
  have h := hq (Nat.lt_succ_self (n + 1))
  linarith

theorem staircase_locally_constant_right (q : ℕ → ℝ)
    (hunbounded : ∀ x : ℝ, ∃ n, x < q n) (x : ℝ) :
    ∃ b > x, ∀ y ∈ Ico x b, staircase q hunbounded y = staircase q hunbounded x := by
  classical
  by_cases hx : x < q 0
  · refine ⟨q 0, hx, ?_⟩
    intro y hy
    simp [staircase, hx, hy.2]
  · refine ⟨nextEvent q hunbounded x, lt_nextEvent q hunbounded x, ?_⟩
    intro y hy
    have hy0 : ¬ y < q 0 := by linarith [hy.1]
    have hindex1 := nextIndex_monotone q hunbounded hy.1
    have hindex2 : nextIndex q hunbounded y ≤ nextIndex q hunbounded x :=
      Nat.find_min' (hunbounded y) hy.2
    have hindex := Nat.le_antisymm hindex1 hindex2
    simp only [staircase, ite_eq_right hx, ite_eq_right hy0, nextEvent, hindex]

theorem staircase_right_continuous (q : ℕ → ℝ)
    (hunbounded : ∀ x : ℝ, ∃ n, x < q n) (x : ℝ) :
    ContinuousWithinAt (staircase q hunbounded) (Ici x) x := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨b, hb, hconst⟩ := staircase_locally_constant_right q hunbounded x
  refine ⟨b - x, sub_pos.mpr hb, ?_⟩
  intro y hy hdist
  have hyx : x ≤ y := hy
  have hyb : y < b := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hyx)] at hdist
    linarith
  rw [hconst y ⟨hyx, hyb⟩]
  simpa using hε

theorem staircase_ratio_tendsto (q : ℕ → ℝ)
    (hunbounded : ∀ x : ℝ, ∃ n, x < q n)
    (hnext : Tendsto (fun x : ℝ => nextEvent q hunbounded x / x) atTop (𝓝 1)) :
    Tendsto (fun x : ℝ => staircase q hunbounded x / x) atTop (𝓝 1) := by
  have hc : Tendsto (fun x : ℝ => q 0 / x) atTop (𝓝 0) :=
    tendsto_id.const_div_atTop (q 0)
  have hsum := hnext.add hc
  simp only [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop (q 0)] with x hx
  simp [staircase, not_lt.mpr hx, add_div]

def staircaseLog (q : ℕ → ℝ) (hunbounded : ∀ x : ℝ, ∃ n, x < q n) (t : ℝ) : ℝ :=
  staircase q hunbounded (Real.exp t)

theorem staircaseLog_monotone (q : ℕ → ℝ)
    (hunbounded : ∀ x : ℝ, ∃ n, x < q n) (hq : Monotone q) (hq0 : 0 ≤ q 0) :
    Monotone (staircaseLog q hunbounded) :=
  (staircase_monotone q hunbounded hq hq0).comp Real.exp_monotone

theorem staircaseLog_weighted_integrable (q : ℕ → ℝ)
    (hunbounded : ∀ x : ℝ, ∃ n, x < q n) (hq : Monotone q) (hq0 : 0 ≤ q 0)
    (a b t : ℝ) :
    IntervalIntegrable
      (fun v : ℝ => (staircaseLog q hunbounded v - Real.exp v) * Real.exp (-v / 2) *
        (1 + (t - v) / 2)) MeasureTheory.volume a b := by
  have hpsi : IntervalIntegrable (staircaseLog q hunbounded) MeasureTheory.volume a b :=
    (staircaseLog_monotone q hunbounded hq hq0).intervalIntegrable
  have he : IntervalIntegrable Real.exp MeasureTheory.volume a b :=
    Real.continuous_exp.intervalIntegrable a b
  apply ((hpsi.sub he).mul_continuousOn ?_).mul_continuousOn ?_
  · apply Continuous.continuousOn
    fun_prop
  · apply Continuous.continuousOn
    fun_prop

theorem staircase_weighted_lower (q : ℕ → ℝ)
    (hunbounded : ∀ x : ℝ, ∃ n, x < q n) (hq : Monotone q) (hq0 : 1 < q 0)
    (t : ℝ) (ht : Real.log (q 0) ≤ t) :
    t + 4 - 4 * Real.exp (Real.log (q 0) / 2) ≤
      PrimeObstruction.weightedError (staircaseLog q hunbounded) t := by
  have hpos : 0 < q 0 := by linarith
  apply PrimeObstruction.weightedError_lower_of_surplus
    (staircaseLog q hunbounded) (Real.log (q 0)) t (Real.log_nonneg hq0.le) ht
  · intro v _
    exact staircase_nonneg q hunbounded hpos.le (Real.exp v)
  · intro v hv
    have hqv : q 0 ≤ Real.exp v := by
      simpa only [Real.exp_log hpos] using Real.exp_le_exp.mpr hv.1
    have hn := lt_nextEvent q hunbounded (Real.exp v)
    simp only [staircaseLog, staircase, ite_eq_right (not_lt.mpr hqv), Real.exp_log hpos]
    linarith
  · exact staircaseLog_weighted_integrable q hunbounded hq hpos.le _ _ t
  · exact staircaseLog_weighted_integrable q hunbounded hq hpos.le _ _ t

theorem staircase_weighted_pos (q : ℕ → ℝ)
    (hunbounded : ∀ x : ℝ, ∃ n, x < q n) (hq : Monotone q) (hq0 : 1 < q 0)
    (t : ℝ) (ht : Real.log (q 0) ≤ t)
    (htlarge : 4 * Real.exp (Real.log (q 0) / 2) ≤ t) :
    0 < PrimeObstruction.weightedError (staircaseLog q hunbounded) t := by
  have h := staircase_weighted_lower q hunbounded hq hq0 t ht
  linarith

theorem staircase_weighted_eventually_pos (q : ℕ → ℝ)
    (hunbounded : ∀ x : ℝ, ∃ n, x < q n) (hq : Monotone q) (hq0 : 1 < q 0) :
    ∀ᶠ t : ℝ in atTop,
      0 < PrimeObstruction.weightedError (staircaseLog q hunbounded) t := by
  filter_upwards [eventually_ge_atTop (Real.log (q 0)),
    eventually_ge_atTop (4 * Real.exp (Real.log (q 0) / 2))] with t ht htlarge
  exact staircase_weighted_pos q hunbounded hq hq0 t ht htlarge

/-- An abstract no-jump argument. Its support hypothesis states that a
counting function is constant before the next event, including at the left
endpoint but excluding the next-event boundary. -/
theorem nextEvent_le_of_noJump_and_error (q : ℕ → ℝ)
    (hunbounded : ∀ x : ℝ, ∃ n, x < q n) (count : ℝ → ℝ)
    (hsupport : ∀ x y : ℝ, x ≤ y → y < nextEvent q hunbounded x → count y = count x)
    (C r x : ℝ) (hC : 0 < C) (hr : 0 < r)
    (hlo : x + 4 * C * r - 2 * C * r ≤ count (x + 4 * C * r))
    (hhi : count x ≤ x + C * r) :
    nextEvent q hunbounded x ≤ x + 4 * C * r := by
  by_contra! hnext
  have hxy : x ≤ x + 4 * C * r := by nlinarith [mul_pos hC hr]
  have heq := hsupport x (x + 4 * C * r) hxy hnext
  rw [heq] at hlo
  nlinarith [mul_pos hC hr]

def pntScale (c x : ℝ) : ℝ := x * Real.exp (-c * Real.sqrt (Real.log x))

theorem pntScale_pos (c x : ℝ) (hx : 0 < x) : 0 < pntScale c x :=
  mul_pos hx (Real.exp_pos _)

theorem pntScale_le_double (c x y : ℝ) (hc : 0 ≤ c) (hx : 0 < x)
    (hxy : x ≤ y) (hy : y ≤ 2 * x) : pntScale c y ≤ 2 * pntScale c x := by
  have hlog := Real.log_le_log hx hxy
  have hsqrt := Real.sqrt_le_sqrt hlog
  have hexp : Real.exp (-c * Real.sqrt (Real.log y)) ≤
      Real.exp (-c * Real.sqrt (Real.log x)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hsqrt (neg_nonpos.mpr hc)
  unfold pntScale
  calc
    y * Real.exp (-c * Real.sqrt (Real.log y)) ≤
        (2 * x) * Real.exp (-c * Real.sqrt (Real.log x)) :=
      mul_le_mul hy hexp (Real.exp_pos _).le (by linarith)
    _ = _ := by ring

/-- Endpoint version of the classical PNT-envelope no-jump argument.
All large-x conditions and the no-event support premise are explicit. -/
theorem nextEvent_gap_of_pnt_envelope (q : ℕ → ℝ)
    (hunbounded : ∀ x : ℝ, ∃ n, x < q n) (count : ℝ → ℝ)
    (hsupport : ∀ x y : ℝ, x ≤ y → y < nextEvent q hunbounded x → count y = count x)
    (C c x : ℝ) (hC : 0 < C) (hc : 0 ≤ c) (hx : 1 ≤ x)
    (hsmall : 4 * C * Real.exp (-c * Real.sqrt (Real.log x)) ≤ 1)
    (hbound : ∀ y : ℝ, x ≤ y → |count y - y| ≤ C * pntScale c y) :
    nextEvent q hunbounded x - x ≤ 4 * C * pntScale c x := by
  have hxpos : 0 < x := by linarith
  have hr := pntScale_pos c x hxpos
  have hxy : x ≤ x + 4 * C * pntScale c x := by nlinarith [mul_pos hC hr]
  have hy : x + 4 * C * pntScale c x ≤ 2 * x := by
    have h := mul_le_mul_of_nonneg_right hsmall hxpos.le
    dsimp [pntScale]
    nlinarith
  have hscale := pntScale_le_double c x (x + 4 * C * pntScale c x) hc hxpos hxy hy
  have hlo := (abs_le.mp (hbound (x + 4 * C * pntScale c x) hxy)).1
  have hhi := (abs_le.mp (hbound x le_rfl)).2
  have h := nextEvent_le_of_noJump_and_error q hunbounded count hsupport C (pntScale c x) x
    hC hr (by nlinarith [mul_le_mul_of_nonneg_left hscale hC.le]) (by linarith)
  linarith

theorem staircase_error_of_gap (q : ℕ → ℝ)
    (hunbounded : ∀ x : ℝ, ∃ n, x < q n) (hq0 : 0 ≤ q 0)
    (C c x : ℝ) (hx : q 0 ≤ x)
    (hgap : nextEvent q hunbounded x - x ≤ 4 * C * pntScale c x) :
    |staircase q hunbounded x - x| ≤ 4 * C * pntScale c x + q 0 := by
  have hn := lt_nextEvent q hunbounded x
  have hnonneg : 0 ≤ staircase q hunbounded x - x := by
    simp only [staircase, ite_eq_right (not_lt.mpr hx)]
    linarith
  rw [abs_of_nonneg hnonneg]
  simp only [staircase, ite_eq_right (not_lt.mpr hx)]
  linarith

theorem nextEvent_ratio_of_pnt_gap (q : ℕ → ℝ)
    (hunbounded : ∀ x : ℝ, ∃ n, x < q n) (C c : ℝ) (hc : 0 < c)
    (hgap : ∀ᶠ x : ℝ in atTop,
      nextEvent q hunbounded x - x ≤ 4 * C * pntScale c x) :
    Tendsto (fun x : ℝ => nextEvent q hunbounded x / x) atTop (𝓝 1) := by
  have hgrowth : Tendsto (fun x : ℝ => c * Real.sqrt (Real.log x)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
  have hexp : Tendsto (fun x : ℝ => Real.exp (-c * Real.sqrt (Real.log x)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hgrowth
  have hlimit : Tendsto (fun x : ℝ => 4 * C * Real.exp (-c * Real.sqrt (Real.log x)))
      atTop (𝓝 0) := by simpa using hexp.const_mul (4 * C)
  have hnonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ (nextEvent q hunbounded x - x) / x := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact div_nonneg (sub_nonneg.mpr (lt_nextEvent q hunbounded x).le) (by linarith)
  have hupper : ∀ᶠ x : ℝ in atTop,
      (nextEvent q hunbounded x - x) / x ≤ 4 * C * Real.exp (-c * Real.sqrt (Real.log x)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), hgap] with x hx hg
    apply (div_le_iff₀ (show 0 < x by linarith)).mpr
    dsimp [pntScale] at hg
    nlinarith
  have hzero := squeeze_zero' hnonneg hupper hlimit
  have hplus := hzero.add_const 1
  simp only [zero_add] at hplus
  apply hplus.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hxne : x ≠ 0 := by linarith
  simp [sub_div, hxne]

theorem staircase_ratio_of_pnt_gap (q : ℕ → ℝ)
    (hunbounded : ∀ x : ℝ, ∃ n, x < q n) (C c : ℝ) (hc : 0 < c)
    (hgap : ∀ᶠ x : ℝ in atTop,
      nextEvent q hunbounded x - x ≤ 4 * C * pntScale c x) :
    Tendsto (fun x : ℝ => staircase q hunbounded x / x) atTop (𝓝 1) :=
  staircase_ratio_tendsto q hunbounded (nextEvent_ratio_of_pnt_gap q hunbounded C c hc hgap)

theorem nextEvent_eventual_gap_of_pnt_envelope (q : ℕ → ℝ)
    (hunbounded : ∀ x : ℝ, ∃ n, x < q n) (count : ℝ → ℝ)
    (hsupport : ∀ x y : ℝ, x ≤ y → y < nextEvent q hunbounded x → count y = count x)
    (C c X : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hbound : ∀ y : ℝ, X ≤ y → |count y - y| ≤ C * pntScale c y) :
    ∀ᶠ x : ℝ in atTop,
      nextEvent q hunbounded x - x ≤ 4 * C * pntScale c x := by
  have hgrowth : Tendsto (fun x : ℝ => c * Real.sqrt (Real.log x)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
  have hexp : Tendsto (fun x : ℝ => Real.exp (-c * Real.sqrt (Real.log x)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hgrowth
  have hlimit : Tendsto (fun x : ℝ => 4 * C * Real.exp (-c * Real.sqrt (Real.log x)))
      atTop (𝓝 0) := by simpa using hexp.const_mul (4 * C)
  have hsmall : ∀ᶠ x : ℝ in atTop,
      4 * C * Real.exp (-c * Real.sqrt (Real.log x)) < 1 :=
    hlimit.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop X, hsmall]
    with x hx hX hsmallx
  exact nextEvent_gap_of_pnt_envelope q hunbounded count hsupport C c x hC hc.le hx hsmallx.le
    (fun y hy => hbound y (le_trans hX hy))

theorem staircase_ratio_of_pnt_count_envelope (q : ℕ → ℝ)
    (hunbounded : ∀ x : ℝ, ∃ n, x < q n) (count : ℝ → ℝ)
    (hsupport : ∀ x y : ℝ, x ≤ y → y < nextEvent q hunbounded x → count y = count x)
    (C c X : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hbound : ∀ y : ℝ, X ≤ y → |count y - y| ≤ C * pntScale c y) :
    Tendsto (fun x : ℝ => staircase q hunbounded x / x) atTop (𝓝 1) :=
  staircase_ratio_of_pnt_gap q hunbounded C c hc
    (nextEvent_eventual_gap_of_pnt_envelope q hunbounded count hsupport C c X hC hc hbound)

/-- The artificial staircase satisfies the coarse asymptotic and support
properties but has an eventually positive weighted error. The event sequence,
supported counting function, and PNT envelope are explicit hypotheses. -/
theorem supported_countermodel (q : ℕ → ℝ)
    (hunbounded : ∀ x : ℝ, ∃ n, x < q n) (hq : StrictMono q) (hq0 : 1 < q 0)
    (count : ℝ → ℝ)
    (hsupport : ∀ x y : ℝ, x ≤ y → y < nextEvent q hunbounded x → count y = count x)
    (C c X : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hbound : ∀ y : ℝ, X ≤ y → |count y - y| ≤ C * pntScale c y) :
    ∃ psi : ℝ → ℝ,
      psi 1 = 0 ∧ Monotone psi ∧ (∀ x : ℝ, 0 ≤ psi x) ∧
      (∀ x : ℝ, ContinuousWithinAt psi (Ici x) x) ∧
      (∀ (n : ℕ) (x : ℝ), x ∈ Ico (q n) (q (n + 1)) → psi x = q (n + 1) + q 0) ∧
      Tendsto (fun x : ℝ => psi x / x) atTop (𝓝 1) ∧
      (∀ᶠ x : ℝ in atTop, |psi x - x| ≤ 4 * C * pntScale c x + q 0) ∧
      (∀ᶠ t : ℝ in atTop, 0 < PrimeObstruction.weightedError (fun v => psi (Real.exp v)) t) := by
  have hzero : 0 ≤ q 0 := by linarith
  refine ⟨staircase q hunbounded, staircase_normalized q hunbounded hq0,
    staircase_monotone q hunbounded hq.monotone hzero,
    staircase_nonneg q hunbounded hzero, staircase_right_continuous q hunbounded,
    staircase_on_event_gap q hunbounded hq,
    staircase_ratio_of_pnt_count_envelope q hunbounded count hsupport C c X hC hc hbound, ?_, ?_⟩
  · have hgap := nextEvent_eventual_gap_of_pnt_envelope q hunbounded count hsupport C c X hC hc hbound
    filter_upwards [eventually_ge_atTop (q 0), hgap] with x hx hg
    exact staircase_error_of_gap q hunbounded hzero C c x hx hg
  · exact staircase_weighted_eventually_pos q hunbounded hq.monotone hq0

#print axioms staircase_normalized
#print axioms event_indices_below_finite
#print axioms event_gaps_cover
#print axioms staircase_monotone
#print axioms staircase_on_event_gap
#print axioms staircase_positive_event_increment
#print axioms staircase_right_continuous
#print axioms staircase_ratio_tendsto
#print axioms staircaseLog_weighted_integrable
#print axioms staircase_weighted_lower
#print axioms staircase_weighted_eventually_pos
#print axioms nextEvent_le_of_noJump_and_error
#print axioms nextEvent_gap_of_pnt_envelope
#print axioms staircase_error_of_gap
#print axioms nextEvent_ratio_of_pnt_gap
#print axioms staircase_ratio_of_pnt_gap
#print axioms nextEvent_eventual_gap_of_pnt_envelope
#print axioms staircase_ratio_of_pnt_count_envelope
#print axioms supported_countermodel

end RhCertificates.PrimeSupport
