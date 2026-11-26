-- Prove2me | solution 1 for ReweightedNPMLE.gamma_coordinate_concentration_of_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:11:52.190549+00:00
-- url     : https://prove2.me/submissions/ce502638-70dd-4a7d-a475-19c63751ad2f

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Tactic
import Theorems.Thm_ReweightedNPMLE_gamma_lower_tail_exact
import Theorems.Thm_ReweightedNPMLE_gamma_upper_tail_exact
import Theorems.Thm_ReweightedNPMLE_neg_sub_log_one_sub_ge_sq_div_two
import Theorems.Thm_ReweightedNPMLE_sub_log_one_add_ge_sq_div_four

/-!
# Gamma moment generating function and coordinate tails

The paper uses shape--rate Gamma variables.  This file connects the scalar
logarithm inequalities in `GammaBounds` to mathlib's actual
`ProbabilityTheory.gammaMeasure`.
-/

open MeasureTheory Real Set
open ProbabilityTheory

open ReweightedNPMLE
open ReweightedNPMLE in
/-- The two-sided Gamma coordinate inequality away from the endpoint. -/
theorem solution {a t : ℝ}
    (ha : 0 < a) (ht₀ : 0 < t) (ht₁ : t < 1) :
    (gammaMeasure a a).real {x | |x - 1| > t} ≤
      2 * Real.exp (-a * t ^ 2 / 4) := by
  letI : IsProbabilityMeasure (gammaMeasure a a) :=
    isProbabilityMeasure_gammaMeasure ha ha
  have ht₀' : 0 ≤ t := ht₀.le
  have hu := gamma_upper_tail_exact ha ht₀'
  have hl := gamma_lower_tail_exact ha ht₀' ht₁
  have hset : {x : ℝ | |x - 1| > t} ⊆
      {x | 1 + t ≤ x} ∪ {x | x ≤ 1 - t} := by
    intro x hx
    change |x - 1| > t at hx
    change (1 + t ≤ x) ∨ (x ≤ 1 - t)
    rcases (lt_abs.mp hx) with hx | hx
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  calc
    (gammaMeasure a a).real {x | |x - 1| > t} ≤
        (gammaMeasure a a).real ({x | 1 + t ≤ x} ∪ {x | x ≤ 1 - t}) :=
      measureReal_mono hset (by finiteness)
    _ ≤ (gammaMeasure a a).real {x | 1 + t ≤ x} +
        (gammaMeasure a a).real {x | x ≤ 1 - t} := measureReal_union_le _ _
    _ ≤ Real.exp (-a * (t - Real.log (1 + t))) +
        Real.exp (-a * (-t - Real.log (1 - t))) := add_le_add hu hl
    _ ≤ 2 * Real.exp (-a * t ^ 2 / 4) := by
      have huLog := sub_log_one_add_ge_sq_div_four ht₀' ht₁.le
      have hlLog : -t - Real.log (1 - t) ≥ t ^ 2 / 4 := by
        exact (neg_sub_log_one_sub_ge_sq_div_two ht₀' ht₁).trans'
          (by nlinarith [sq_nonneg t])
      have hua : -a * (t - Real.log (1 + t)) ≤ -a * t ^ 2 / 4 := by
        nlinarith
      have hla : -a * (-t - Real.log (1 - t)) ≤ -a * t ^ 2 / 4 := by
        nlinarith
      rw [two_mul]
      exact add_le_add (Real.exp_le_exp.mpr hua) (Real.exp_le_exp.mpr hla)
