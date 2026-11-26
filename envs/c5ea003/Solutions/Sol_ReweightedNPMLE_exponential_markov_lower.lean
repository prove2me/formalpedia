-- Prove2me | solution 1 for ReweightedNPMLE.exponential_markov_lower
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:06:40.212905+00:00
-- url     : https://prove2.me/submissions/71a9a0bf-6648-400e-bf83-f4e40472b284

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Tactic
import Theorems.Thm_ReweightedNPMLE_exponential_markov_upper

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
/-- Lower-tail version of exponential Markov, using a positive tilt of `-X`. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) {s c : ℝ} (hs : 0 < s)
    (hint : Integrable (fun ω ↦ Real.exp (-s * X ω)) μ) :
    μ.real {ω | X ω ≤ -c} ≤
      Real.exp (-s * c) * ∫ ω, Real.exp (-s * X ω) ∂μ := by
  have hfun : (fun ω ↦ Real.exp (s * (-X ω))) =
      (fun ω ↦ Real.exp (-s * X ω)) := by
    funext ω
    congr 1
    ring
  have hset : {ω | c ≤ -X ω} = {ω | X ω ≤ -c} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor <;> intro hω <;> linarith
  have hint' : Integrable (fun ω ↦ Real.exp (s * (-X ω))) μ := by
    rw [hfun]
    exact hint
  have h := exponential_markov_upper μ (fun ω ↦ -X ω) hs hint'
    (c := c)
  rw [hset, hfun] at h
  exact h
