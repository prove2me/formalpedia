-- Prove2me | solution 1 for ReweightedNPMLE.integrableOn_rpow_mul_exp_neg_mul_Ioi
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:09:06.689573+00:00
-- url     : https://prove2.me/submissions/18bf0381-a98f-4a44-a064-f786c5ca9a3e

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Tactic

/-!
# Gamma moment generating function and coordinate tails

The paper uses shape--rate Gamma variables.  This file connects the scalar
logarithm inequalities in `GammaBounds` to mathlib's actual
`ProbabilityTheory.gammaMeasure`.
-/

open MeasureTheory Real Set
open ProbabilityTheory
/-- The basic Gamma-kernel integrability lemma on the positive half-line. -/
theorem solution {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) :
    IntegrableOn (fun x : ℝ ↦ x ^ (a - 1) * Real.exp (-(r * x))) (Ioi 0) := by
  let f : ℝ → ℝ := fun y ↦ Real.exp (-y) * y ^ (a - 1)
  have hcomp : IntegrableOn (fun x ↦ f (r * x)) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff f 0 hr).2
    simpa [f] using Real.GammaIntegral_convergent ha
  have hrpow : r ^ (a - 1) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
  have hscaled := hcomp.const_mul (r ^ (a - 1))⁻¹
  apply IntegrableOn.congr_fun hscaled _ measurableSet_Ioi
  intro x hx
  dsimp [f]
  rw [Real.mul_rpow hr.le hx.le]
  field_simp
