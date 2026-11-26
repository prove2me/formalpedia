-- Prove2me | solution 1 for ReweightedNPMLE.exponential_markov_upper
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:06:04.415844+00:00
-- url     : https://prove2.me/submissions/afc3f50b-3837-4b2a-9a2b-46660fa7aca0

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
/-- Exponential Markov inequality, expressed using `Measure.real`. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) {s c : ℝ} (hs : 0 < s)
    (hint : Integrable (fun ω ↦ Real.exp (s * X ω)) μ) :
    μ.real {ω | c ≤ X ω} ≤
      Real.exp (-s * c) * ∫ ω, Real.exp (s * X ω) ∂μ := by
  have hset : {ω | Real.exp (s * c) ≤ Real.exp (s * X ω)} =
      {ω | c ≤ X ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Real.exp_le_exp]
    constructor <;> intro hω <;> nlinarith
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun ω ↦ Real.exp (s * X ω))
    (Filter.Eventually.of_forall fun ω ↦ (Real.exp_pos _).le) hint (Real.exp (s * c))
  rw [hset] at hmarkov
  calc
    μ.real {ω | c ≤ X ω} =
        Real.exp (-s * c) *
          (Real.exp (s * c) * μ.real {ω | c ≤ X ω}) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    _ ≤ Real.exp (-s * c) * ∫ ω, Real.exp (s * X ω) ∂μ :=
      mul_le_mul_of_nonneg_left hmarkov (Real.exp_pos _).le
