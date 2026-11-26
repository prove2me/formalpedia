-- Prove2me | solution 1 for ReweightedNPMLE.centered_gamma_mgf
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:03:10.89311+00:00
-- url     : https://prove2.me/submissions/251d4433-540a-4955-b1c1-8f0792ce644f

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Tactic
import Theorems.Thm_ReweightedNPMLE_integral_exp_mul_gammaMeasure

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









/-- Closed form of the Gamma moment-generating function. -/
theorem gamma_mgf {a r t : ℝ} (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
    ∫ x, Real.exp (t * x) ∂gammaMeasure a r = (r / (r - t)) ^ a := by
  rw [integral_exp_mul_gammaMeasure ha hr ht]
  have hG : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  calc
    r ^ a / Real.Gamma a * (1 / (r - t)) ^ a * Real.Gamma a =
        r ^ a * (1 / (r - t)) ^ a := by field_simp
    _ = (r * (1 / (r - t))) ^ a := by
      rw [Real.mul_rpow hr.le (by positivity)]
    _ = (r / (r - t)) ^ a := by simp [div_eq_mul_inv]



































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
/-- MGF of a centered `Gamma(a,a)` variable. -/
theorem solution {a t : ℝ} (ha : 0 < a) (ht : t < a) :
    ∫ x, Real.exp (t * (x - 1)) ∂gammaMeasure a a =
      Real.exp (-t) * (1 - t / a) ^ (-a) := by
  have hprob : IsProbabilityMeasure (gammaMeasure a a) :=
    isProbabilityMeasure_gammaMeasure ha ha
  calc
    ∫ x, Real.exp (t * (x - 1)) ∂gammaMeasure a a =
        ∫ x, Real.exp (-t) * Real.exp (t * x) ∂gammaMeasure a a := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x ↦ by
            change Real.exp (t * (x - 1)) = Real.exp (-t) * Real.exp (t * x)
            rw [← Real.exp_add]
            congr 1
            ring
    _ = Real.exp (-t) * ∫ x, Real.exp (t * x) ∂gammaMeasure a a := by
      rw [integral_const_mul]
    _ = Real.exp (-t) * (a / (a - t)) ^ a := by
      rw [gamma_mgf ha ha ht]
    _ = Real.exp (-t) * (1 - t / a) ^ (-a) := by
      congr 1
      have hbase : 0 < 1 - t / a := by
        rw [sub_pos, div_lt_one ha]
        exact ht
      have hbaseeq : a / (a - t) = (1 - t / a)⁻¹ := by
        field_simp [ha.ne']
      rw [hbaseeq, Real.inv_rpow hbase.le, Real.rpow_neg hbase.le]
