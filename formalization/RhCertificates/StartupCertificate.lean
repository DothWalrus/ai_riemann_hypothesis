module

public import RhCertificates.StartupFiniteBounds
public import RhCertificates.StartupConstants
public import RhCertificates.StartupGeometry
public import RhCertificates.PrimeStartup
public import RhCertificates.StartupSourceSum

/-!
A certificate for the explicit series and for a transcription of equation
(1.5), using the actual digamma constant, convergent Lerch defining series
and von Mangoldt weights. The paper's global RH criterion and zero expansion
are not proved here. In particular this is not a proof of RH.
-/

public section

namespace RhCertificates

theorem smoothPart_negative_of_constant_bounds (C : ℝ)
    (hClo : (67 : ℝ) / 25 < C) (hChi : C < (2691 : ℝ) / 1000) :
    ∀ t : ℝ, 0 < t → SmoothSeries.smoothPart C t < 0 := by
  have hvalue := SmoothSeries.smoothPart_half_lt_coarse C hChi.le
  have hslope := SmoothSeries.smoothDerivative_half_coarse_bounds C hClo hChi
  apply startup_negative_of_curvature_formula_margin
    (SmoothSeries.smoothPart C) (SmoothSeries.smoothDerivative C ((1 : ℝ) / 2))
    (SmoothSeries.continuousOn_smoothPart C)
    (SmoothSeries.differentiableOn_smoothPart C)
    (SmoothSeries.differentiableOn_smoothPart_deriv C)
    (SmoothSeries.smoothPart_second_deriv C)
    (SmoothSeries.smoothPart_zero C)
    (SmoothSeries.smoothPart_hasDerivAt C ((1 : ℝ) / 2) (by norm_num))
  · linarith
  · exact hslope.2.le

/-- The explicitly defined gamma/pi/log constant meets all needed bounds. -/
theorem smoothPart_startupConstant_negative :
    ∀ t : ℝ, 0 < t → SmoothSeries.smoothPart startupConstant t < 0 :=
  smoothPart_negative_of_constant_bounds startupConstant
    startupConstant_bounds.1 startupConstant_bounds.2

/-- The finite contribution vanishes on this interval for every weight
function. This certifies the displayed formula, not an unstated zeta identity. -/
theorem fullExpression_startupConstant_negative (weight : ℕ → ℝ) :
    ∀ t : ℝ, 0 < t → t ≤ Real.log 2 →
      PrimeStartup.fullExpression startupConstant weight t < 0 :=
  PrimeStartup.fullExpression_negative_on_startup startupConstant weight
    smoothPart_startupConstant_negative

/-- Strict startup sign for the positive-integer-sum source formula. -/
theorem sourceFormula_negative_on_startup (t : ℝ)
    (ht : 0 < t) (hcutoff : t ≤ Real.log 2) :
    StartupSourceSum.sourceFormula t < 0 := by
  rw [StartupSourceSum.sourceFormula_eq_sourceFullExpression,
    StartupLerch.sourceFullExpression_eq_fullExpression t ht.le]
  exact fullExpression_startupConstant_negative StartupLerch.actualPrimeWeight t ht hcutoff

theorem sourceFormula_zero : StartupSourceSum.sourceFormula 0 = 0 := by
  rw [StartupSourceSum.sourceFormula_eq_sourceFullExpression,
    StartupLerch.sourceFullExpression_eq_fullExpression 0 le_rfl,
    PrimeStartup.fullExpression_eq_smoothPart startupConstant StartupLerch.actualPrimeWeight 0
      (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))]
  exact SmoothSeries.smoothPart_zero startupConstant

#print axioms smoothPart_negative_of_constant_bounds
#print axioms smoothPart_startupConstant_negative
#print axioms fullExpression_startupConstant_negative
#print axioms sourceFormula_negative_on_startup
#print axioms sourceFormula_zero

end RhCertificates
