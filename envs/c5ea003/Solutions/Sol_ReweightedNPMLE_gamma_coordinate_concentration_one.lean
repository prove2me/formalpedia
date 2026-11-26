-- Prove2me | solution 1 for ReweightedNPMLE.gamma_coordinate_concentration_one
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:11:54.992688+00:00
-- url     : https://prove2.me/submissions/10ddb07c-f69b-47f5-bf47-a9027de29ddb

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Tactic
import Theorems.Thm_ReweightedNPMLE_gamma_upper_tail_exact
import Theorems.Thm_ReweightedNPMLE_sub_log_one_add_ge_sq_div_four

-- Inline helpers preserved from ReweightedNPMLE.GammaDistribution.
section
/-!
# Gamma moment generating function and coordinate tails

The paper uses shape--rate Gamma variables.  This file connects the scalar
logarithm inequalities in `GammaBounds` to mathlib's actual
`ProbabilityTheory.gammaMeasure`.
-/

open MeasureTheory Real Set
open ProbabilityTheory

namespace ReweightedNPMLE

































/-- A Gamma law assigns zero mass to the nonpositive half-line. -/
theorem gammaMeasure_Iic_zero {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    gammaMeasure a r (Iic 0) = 0 := by
  rw [gammaMeasure, withDensity_apply _ measurableSet_Iic,
    lintegral_Iic_eq_lintegral_Iio_add_Icc (f := gammaPDF a r) le_rfl,
    lintegral_gammaPDF_of_nonpos le_rfl]
  simp











end ReweightedNPMLE
end

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
/-- Endpoint `t = 1`, where the lower tail is empty up to a null singleton. -/
theorem solution {a : ℝ} (ha : 0 < a) :
    (gammaMeasure a a).real {x | |x - 1| > 1} ≤
      2 * Real.exp (-a / 4) := by
  letI : IsProbabilityMeasure (gammaMeasure a a) :=
    isProbabilityMeasure_gammaMeasure ha ha
  have hu := gamma_upper_tail_exact ha (show (0 : ℝ) ≤ 1 by norm_num)
  have hzero : (gammaMeasure a a).real {x | x ≤ 0} = 0 := by
    change ENNReal.toReal (gammaMeasure a a (Iic 0)) = 0
    rw [gammaMeasure_Iic_zero ha ha]
    simp
  have hset : {x : ℝ | |x - 1| > 1} ⊆ {x | 2 ≤ x} ∪ {x | x ≤ 0} := by
    intro x hx
    change |x - 1| > 1 at hx
    change (2 ≤ x) ∨ (x ≤ 0)
    rcases (lt_abs.mp hx) with hx | hx
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hu' : (gammaMeasure a a).real {x | 2 ≤ x} ≤
      Real.exp (-a * (1 - Real.log 2)) := by norm_num at hu ⊢; exact hu
  have hlog := sub_log_one_add_ge_sq_div_four
    (show (0 : ℝ) ≤ 1 by norm_num) (show (1 : ℝ) ≤ 1 by norm_num)
  have hexp : Real.exp (-a * (1 - Real.log 2)) ≤ Real.exp (-a / 4) := by
    apply Real.exp_le_exp.mpr
    norm_num at hlog
    nlinarith
  calc
    (gammaMeasure a a).real {x | |x - 1| > 1} ≤
        (gammaMeasure a a).real ({x | 2 ≤ x} ∪ {x | x ≤ 0}) :=
      measureReal_mono hset (by finiteness)
    _ ≤ (gammaMeasure a a).real {x | 2 ≤ x} +
        (gammaMeasure a a).real {x | x ≤ 0} := measureReal_union_le _ _
    _ ≤ Real.exp (-a * (1 - Real.log 2)) + 0 := add_le_add hu' hzero.le
    _ ≤ 2 * Real.exp (-a / 4) := by nlinarith [Real.exp_pos (-a / 4), hexp]
