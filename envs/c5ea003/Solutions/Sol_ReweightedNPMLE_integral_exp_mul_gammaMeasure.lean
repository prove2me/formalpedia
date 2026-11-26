-- Prove2me | solution 1 for ReweightedNPMLE.integral_exp_mul_gammaMeasure
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:02:24.788905+00:00
-- url     : https://prove2.me/submissions/4bcbc584-d5ca-4a4c-989e-dcb6c07d3a55

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Tactic

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

private theorem gammaPDF_toReal {a r x : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (gammaPDF a r x).toReal = gammaPDFReal a r x := by
  rw [gammaPDF]
  exact ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x)











































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
/-- The (uncentered) moment-generating integral of a shape--rate Gamma law. -/
theorem solution {a r t : ℝ}
    (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
    ∫ x, Real.exp (t * x) ∂gammaMeasure a r =
      r ^ a / Real.Gamma a * (1 / (r - t)) ^ a * Real.Gamma a := by
  rw [gammaMeasure, integral_withDensity_eq_integral_toReal_smul]
  · change (∫ x, (gammaPDF a r x).toReal * Real.exp (t * x)) = _
    simp_rw [gammaPDF_toReal ha hr]
    have hsupport : (Set.indicator (Ici (0 : ℝ)) fun x ↦
        gammaPDFReal a r x * Real.exp (t * x)) =
        (fun x ↦ gammaPDFReal a r x * Real.exp (t * x)) := by
      funext x
      by_cases hx : x ∈ Ici (0 : ℝ)
      · exact Set.indicator_of_mem hx _
      · have hxneg : x < 0 := not_le.mp hx
        simp [hx, gammaPDFReal, if_neg (not_le.mpr hxneg)]
    rw [← hsupport, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
    have hfun : ∫ x in Ioi (0 : ℝ), gammaPDFReal a r x * Real.exp (t * x) =
        ∫ x in Ioi (0 : ℝ), (r ^ a / Real.Gamma a) *
          (x ^ (a - 1) * Real.exp (-((r - t) * x))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hxnonneg : 0 ≤ x := hx.le
      simp only [gammaPDFReal, if_pos hxnonneg]
      have hexp : Real.exp (-(r * x)) * Real.exp (t * x) =
          Real.exp (-((r - t) * x)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        r ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-(r * x)) *
            Real.exp (t * x) =
            (r ^ a / Real.Gamma a) * x ^ (a - 1) *
              (Real.exp (-(r * x)) * Real.exp (t * x)) := by ring
        _ = (r ^ a / Real.Gamma a) *
            (x ^ (a - 1) * Real.exp (-((r - t) * x))) := by rw [hexp]; ring
    rw [hfun, integral_const_mul,
      Real.integral_rpow_mul_exp_neg_mul_Ioi ha (sub_pos.mpr ht)]
    ring
  · exact (measurable_gammaPDFReal a r).ennreal_ofReal
  · exact Filter.Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top
