module

public import Mathlib.Analysis.Convex.Deriv
public import RhCertificates.Tangent
public import RhCertificates.Curvature

/-!
The geometric component of the startup argument.

The theorems below concern an arbitrary real function. Convexity, concavity,
the derivative, and the numerical bounds are explicit hypotheses. No theorem
here establishes those hypotheses for the actual Nakamura--Suzuki function.
-/

public section

open Set

namespace RhCertificates

/-- A differentiable concave function lies below its tangent on its domain. -/
theorem concave_le_tangent
    {S : Set ℝ} {f : ℝ → ℝ} {s t d : ℝ}
    (hc : ConcaveOn ℝ S f) (hs : s ∈ S) (ht : t ∈ S)
    (hd : HasDerivAt f d s) :
    f t ≤ f s + d * (t - s) := by
  rcases lt_trichotomy s t with hst | hst | hts
  · have h := hc.slope_le_of_hasDerivAt hs ht hst hd
    rw [slope_def_field] at h
    have hp : 0 < t - s := sub_pos.mpr hst
    have hmul := (div_le_iff₀ hp).mp h
    nlinarith
  · subst t
    simp
  · have h := hc.le_slope_of_hasDerivAt ht hs hts hd
    rw [slope_def_field] at h
    have hp : 0 < s - t := sub_pos.mpr hts
    have hmul := (le_div_iff₀ hp).mp h
    nlinarith

/-- A convex function with zero initial value and negative final value is
strictly negative at every positive point of that interval. -/
theorem convex_negative_of_zero_and_negative_endpoint
    {f : ℝ → ℝ} {a t : ℝ}
    (ha : 0 < a) (hc : ConvexOn ℝ (Icc 0 a) f)
    (hzero : f 0 = 0) (hend : f a < 0)
    (ht : 0 < t) (hta : t ≤ a) :
    f t < 0 := by
  have hweight_pos : 0 < t / a := div_pos ht ha
  have hweight_le : t / a ≤ 1 := (div_le_one ha).mpr hta
  have hcombo : (1 - t / a) * 0 + (t / a) * a = t := by
    field_simp
    ring
  have h := hc.2 (show (0 : ℝ) ∈ Icc 0 a from ⟨le_rfl, le_of_lt ha⟩)
    (show a ∈ Icc 0 a from ⟨le_of_lt ha, le_rfl⟩)
    (sub_nonneg.mpr hweight_le) (le_of_lt hweight_pos)
    (show 1 - t / a + t / a = 1 by ring)
  simp only [smul_eq_mul] at h
  rw [hcombo, hzero, mul_zero, zero_add] at h
  exact lt_of_le_of_lt h (mul_neg_of_pos_of_neg hweight_pos hend)

/-- Conditional startup geometry: a convex initial part and a concave tail
with the specified tangent data imply strict negativity at every positive
argument. The hypotheses remain to be proved for the actual smooth part. -/
theorem startup_negative_of_convex_concave
    (f : ℝ → ℝ) (a d : ℝ)
    (ha_lower : (1 : ℝ) / 4 < a)
    (ha_upper : a ≤ (1 : ℝ) / 2)
    (hconvex : ConvexOn ℝ (Icc 0 a) f)
    (hconcave : ConcaveOn ℝ (Ici a) f)
    (hzero : f 0 = 0)
    (hderiv : HasDerivAt f d ((1 : ℝ) / 2))
    (hvalue : f ((1 : ℝ) / 2) < -(1 : ℝ) / 40)
    (hd_lower : -(1 : ℝ) / 32 < d)
    (hd_upper : d < 0) :
    ∀ t : ℝ, 0 < t → f t < 0 := by
  have htail : ∀ t : ℝ, a ≤ t → f t < 0 := by
    intro t ht
    have htan := concave_le_tangent hconcave ha_upper ht hderiv
    have harith := tangent_negative (f ((1 : ℝ) / 2)) d t
      hvalue hd_lower hd_upper (by linarith)
    exact lt_of_le_of_lt htan harith
  intro t ht
  by_cases hta : a ≤ t
  · exact htail t hta
  · exact convex_negative_of_zero_and_negative_endpoint (by linarith)
      hconvex hzero (htail a le_rfl) ht (le_of_not_ge hta)

/-- A curvature formulation of the same conditional argument. Differentiability
is required only on the positive half-line: no derivative at zero is assumed.
Continuity at zero is retained to justify convexity on the closed initial
interval and the endpoint chord. -/
theorem startup_negative_of_second_derivative_signs
    (f : ℝ → ℝ) (a d : ℝ)
    (ha_lower : (1 : ℝ) / 4 < a)
    (ha_upper : a ≤ (1 : ℝ) / 2)
    (hcontinuous : ContinuousOn f (Ici 0))
    (hdifferentiable : DifferentiableOn ℝ f (Ioi 0))
    (hderiv_differentiable : DifferentiableOn ℝ (deriv f) (Ioi 0))
    (hcurvature_left : ∀ x : ℝ, 0 < x → x < a → 0 ≤ deriv (deriv f) x)
    (hcurvature_right : ∀ x : ℝ, a < x → deriv (deriv f) x ≤ 0)
    (hzero : f 0 = 0)
    (hderiv : HasDerivAt f d ((1 : ℝ) / 2))
    (hvalue : f ((1 : ℝ) / 2) < -(1 : ℝ) / 40)
    (hd_lower : -(1 : ℝ) / 32 < d)
    (hd_upper : d < 0) :
    ∀ t : ℝ, 0 < t → f t < 0 := by
  have ha_pos : 0 < a := by linarith
  have hconvex : ConvexOn ℝ (Icc 0 a) f := by
    apply convexOn_of_deriv2_nonneg (D := Icc 0 a) (convex_Icc 0 a)
      (hcontinuous.mono (fun _ hx => hx.1))
    · rw [interior_Icc]
      exact hdifferentiable.mono (fun _ hx => hx.1)
    · rw [interior_Icc]
      exact hderiv_differentiable.mono (fun _ hx => hx.1)
    · intro x hx
      rw [interior_Icc] at hx
      exact hcurvature_left x hx.1 hx.2
  have hconcave : ConcaveOn ℝ (Ici a) f := by
    apply concaveOn_of_deriv2_nonpos (D := Ici a) (convex_Ici a)
      (hcontinuous.mono (fun _ hx => le_trans (le_of_lt ha_pos) hx))
    · rw [interior_Ici]
      exact hdifferentiable.mono (fun _ hx => lt_trans ha_pos hx)
    · rw [interior_Ici]
      exact hderiv_differentiable.mono (fun _ hx => lt_trans ha_pos hx)
    · intro x hx
      rw [interior_Ici] at hx
      exact hcurvature_right x hx
  exact startup_negative_of_convex_concave f a d ha_lower ha_upper
    hconvex hconcave hzero hderiv hvalue hd_lower hd_upper

/-- If the displayed second-derivative formula is established for a smooth
function, its curvature transition and the needed convex/concave geometry
are consequences rather than additional assumptions. -/
theorem startup_negative_of_curvature_formula
    (f : ℝ → ℝ) (d : ℝ)
    (hcontinuous : ContinuousOn f (Ici 0))
    (hdifferentiable : DifferentiableOn ℝ f (Ioi 0))
    (hderiv_differentiable : DifferentiableOn ℝ (deriv f) (Ioi 0))
    (hcurvature : ∀ t : ℝ, 0 < t →
      deriv (deriv f) t =
        -Real.exp (t / 2) + Real.exp (-t / 2) / (Real.exp (2 * t) - 1))
    (hzero : f 0 = 0)
    (hderiv : HasDerivAt f d ((1 : ℝ) / 2))
    (hvalue : f ((1 : ℝ) / 2) < -(1 : ℝ) / 40)
    (hd_lower : -(1 : ℝ) / 32 < d)
    (hd_upper : d < 0) :
    ∀ t : ℝ, 0 < t → f t < 0 := by
  obtain ⟨a, ha_lower, ha_upper, hleft, hright⟩ :=
    exists_exponential_curvature_transition
  apply startup_negative_of_second_derivative_signs f a d ha_lower
    (by linarith) hcontinuous hdifferentiable hderiv_differentiable
    (hzero := hzero) (hderiv := hderiv) (hvalue := hvalue)
    (hd_lower := hd_lower) (hd_upper := hd_upper)
  · intro x hx hxa
    rw [hcurvature x hx]
    exact hleft x hx (le_of_lt hxa)
  · intro x hax
    have hx : 0 < x := by linarith
    rw [hcurvature x hx]
    exact hright x (le_of_lt hax)

/-- A flexible tangent margin, without prescribing separate rational bounds
on the intercept and slope. -/
theorem tangent_negative_of_margin (h d t : ℝ)
    (hmargin : h - d / 4 < 0) (hd : d ≤ 0)
    (ht : (1 : ℝ) / 4 ≤ t) :
    h + d * (t - (1 : ℝ) / 2) < 0 := by
  have hproduct : d * (t - (1 : ℝ) / 4) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hd (sub_nonneg.mpr ht)
  nlinarith

/-- Convex/chord and concave/tangent geometry with a single exact margin. -/
theorem startup_negative_of_convex_concave_margin
    (f : ℝ → ℝ) (a d : ℝ)
    (ha_lower : (1 : ℝ) / 4 < a)
    (ha_upper : a ≤ (1 : ℝ) / 2)
    (hconvex : ConvexOn ℝ (Icc 0 a) f)
    (hconcave : ConcaveOn ℝ (Ici a) f)
    (hzero : f 0 = 0)
    (hderiv : HasDerivAt f d ((1 : ℝ) / 2))
    (hmargin : f ((1 : ℝ) / 2) - d / 4 < 0)
    (hd : d ≤ 0) :
    ∀ t : ℝ, 0 < t → f t < 0 := by
  have htail : ∀ t : ℝ, a ≤ t → f t < 0 := by
    intro t ht
    have htan := concave_le_tangent hconcave ha_upper ht hderiv
    have harith := tangent_negative_of_margin (f ((1 : ℝ) / 2)) d t
      hmargin hd (by linarith)
    exact lt_of_le_of_lt htan harith
  intro t ht
  by_cases hta : a ≤ t
  · exact htail t hta
  · exact convex_negative_of_zero_and_negative_endpoint (by linarith)
      hconvex hzero (htail a le_rfl) ht (le_of_not_ge hta)

/-- The checked exponential curvature transition, followed by the flexible
tangent margin, proves strict negativity on the positive half-line. -/
theorem startup_negative_of_curvature_formula_margin
    (f : ℝ → ℝ) (d : ℝ)
    (hcontinuous : ContinuousOn f (Ici 0))
    (hdifferentiable : DifferentiableOn ℝ f (Ioi 0))
    (hderiv_differentiable : DifferentiableOn ℝ (deriv f) (Ioi 0))
    (hcurvature : ∀ t : ℝ, 0 < t →
      deriv (deriv f) t =
        -Real.exp (t / 2) + Real.exp (-t / 2) / (Real.exp (2 * t) - 1))
    (hzero : f 0 = 0)
    (hderiv : HasDerivAt f d ((1 : ℝ) / 2))
    (hmargin : f ((1 : ℝ) / 2) - d / 4 < 0)
    (hd : d ≤ 0) :
    ∀ t : ℝ, 0 < t → f t < 0 := by
  obtain ⟨a, ha_lower, ha_upper, hleft, hright⟩ :=
    exists_exponential_curvature_transition
  have ha_pos : 0 < a := by linarith
  have hconvex : ConvexOn ℝ (Icc 0 a) f := by
    apply convexOn_of_deriv2_nonneg (D := Icc 0 a) (convex_Icc 0 a)
      (hcontinuous.mono (fun _ hx => hx.1))
    · rw [interior_Icc]
      exact hdifferentiable.mono (fun _ hx => hx.1)
    · rw [interior_Icc]
      exact hderiv_differentiable.mono (fun _ hx => hx.1)
    · intro x hx
      rw [interior_Icc] at hx
      change 0 ≤ deriv (deriv f) x
      rw [hcurvature x hx.1]
      exact hleft x hx.1 (le_of_lt hx.2)
  have hconcave : ConcaveOn ℝ (Ici a) f := by
    apply concaveOn_of_deriv2_nonpos (D := Ici a) (convex_Ici a)
      (hcontinuous.mono (fun _ hx => le_trans (le_of_lt ha_pos) hx))
    · rw [interior_Ici]
      exact hdifferentiable.mono (fun _ hx => lt_trans ha_pos hx)
    · rw [interior_Ici]
      exact hderiv_differentiable.mono (fun _ hx => lt_trans ha_pos hx)
    · intro x hx
      rw [interior_Ici] at hx
      change deriv (deriv f) x ≤ 0
      rw [hcurvature x (lt_trans ha_pos hx)]
      exact hright x (le_of_lt hx)
  exact startup_negative_of_convex_concave_margin f a d ha_lower
    (by linarith) hconvex hconcave hzero hderiv hmargin hd

#print axioms concave_le_tangent
#print axioms convex_negative_of_zero_and_negative_endpoint
#print axioms startup_negative_of_convex_concave
#print axioms startup_negative_of_second_derivative_signs
#print axioms startup_negative_of_curvature_formula
#print axioms tangent_negative_of_margin
#print axioms startup_negative_of_convex_concave_margin
#print axioms startup_negative_of_curvature_formula_margin

end RhCertificates
