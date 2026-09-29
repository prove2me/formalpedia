-- Prove2me | solution 1 for ProbabilityTheory.integrable_of_integrable_sq
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-16T01:23:50.072971+00:00
-- url     : https://prove2.me/submissions/2344540b-6db0-4271-a602-6b04b440b222

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 2000000

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (hZ : Measurable Z) (hsq : Integrable (fun ω => (Z ω) ^ 2) μ) :
    Integrable Z μ := by
  have h1 : Integrable (fun ω => (1 + (Z ω) ^ 2) / 2) μ :=
    (((integrable_const (1 : ℝ)).add hsq)).div_const 2
  refine Integrable.mono h1 hZ.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  have hnn : (0 : ℝ) ≤ (1 + (Z ω) ^ 2) / 2 := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn]
  nlinarith [sq_nonneg (|Z ω| - 1), sq_abs (Z ω), abs_nonneg (Z ω)]

