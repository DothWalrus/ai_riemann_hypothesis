module

public import RhCertificates.StartupLerch
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
Literal positive-integer finite-sum transcription of the source formula.
The n=1 term vanishes; the argument covers empty cutoffs as well.
-/

@[expose] public section
noncomputable section

namespace RhCertificates.StartupSourceSum

def sourceFormula (t : ℝ) : ℝ :=
  StartupLerch.sourceSmoothExpression t +
    ∑ n ∈ Finset.Icc 1 ⌊Real.exp t⌋₊,
      StartupLerch.actualPrimeWeight n * (t - Real.log (n : ℝ))

theorem positive_sum_eq_normalized_sum (N : ℕ) (t : ℝ) :
    (∑ n ∈ Finset.Icc 1 N,
      StartupLerch.actualPrimeWeight n * (t - Real.log (n : ℝ))) =
    ∑ n ∈ Finset.Icc 2 N,
      StartupLerch.actualPrimeWeight n * (t - Real.log (n : ℝ)) := by
  have hsub : Finset.Icc 2 N ⊆ Finset.Icc 1 N := by
    intro n hn
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, hhi⟩
  have hsum := Finset.sum_subset hsub (f := fun n : ℕ =>
    StartupLerch.actualPrimeWeight n * (t - Real.log (n : ℝ))) (by
      intro n hn hnot
      obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
      have hnlt : n < 2 := by
        by_contra! hge
        exact hnot (Finset.mem_Icc.mpr ⟨hge, hhi⟩)
      have heq : n = 1 := by omega
      subst n
      rw [StartupLerch.actualPrimeWeight_one, zero_mul])
  exact hsum.symm

theorem sourceFormula_eq_sourceFullExpression (t : ℝ) :
    sourceFormula t = StartupLerch.sourceFullExpression t := by
  rw [sourceFormula, StartupLerch.sourceFullExpression,
    PrimeStartup.primeContribution, positive_sum_eq_normalized_sum]

#print axioms positive_sum_eq_normalized_sum
#print axioms sourceFormula_eq_sourceFullExpression

end RhCertificates.StartupSourceSum
