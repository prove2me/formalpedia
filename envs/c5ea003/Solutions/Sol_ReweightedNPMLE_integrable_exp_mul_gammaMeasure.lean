-- Prove2me | solution 1 for ReweightedNPMLE.integrable_exp_mul_gammaMeasure
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:09:33.621412+00:00
-- url     : https://prove2.me/submissions/edfd893a-612b-4485-8de4-f48f918d0bc6

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Tactic
import Theorems.Thm_ReweightedNPMLE_integrableOn_rpow_mul_exp_neg_mul_Ioi

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
/-- Exponential moments below the rate are integrable under a Gamma law. -/
theorem solution {a r t : ℝ}
    (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
    Integrable (fun x ↦ Real.exp (t * x)) (gammaMeasure a r) := by
  rw [gammaMeasure]
  change Integrable (fun x ↦ Real.exp (t * x))
    (volume.withDensity (fun x ↦ ENNReal.ofReal (gammaPDFReal a r x)))
  rw [integrable_withDensity_iff
    (measurable_gammaPDFReal a r).ennreal_ofReal
    (Filter.Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top)]
  have hsupport : (fun x ↦ Real.exp (t * x) * gammaPDFReal a r x) =
      Set.indicator (Ici (0 : ℝ)) (fun x ↦
        (r ^ a / Real.Gamma a) *
          (x ^ (a - 1) * Real.exp (-((r - t) * x)))) := by
    funext x
    by_cases hx : 0 ≤ x
    · simp only [gammaPDFReal, if_pos hx]
      have hxIci : x ∈ Ici (0 : ℝ) := hx
      rw [Set.indicator_of_mem hxIci]
      have hexp : Real.exp (t * x) * Real.exp (-(r * x)) =
          Real.exp (-((r - t) * x)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        Real.exp (t * x) *
            (r ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-(r * x))) =
            (r ^ a / Real.Gamma a) * x ^ (a - 1) *
              (Real.exp (t * x) * Real.exp (-(r * x))) := by ring
        _ = (r ^ a / Real.Gamma a) *
            (x ^ (a - 1) * Real.exp (-((r - t) * x))) := by rw [hexp]; ring
    · have hxmem : x ∉ Ici (0 : ℝ) := hx
      simp [gammaPDFReal, hx, hxmem]
  simp_rw [ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _)]
  rw [hsupport, integrable_indicator_iff measurableSet_Ici,
    integrableOn_Ici_iff_integrableOn_Ioi]
  exact (integrableOn_rpow_mul_exp_neg_mul_Ioi ha (sub_pos.mpr ht)).const_mul _
