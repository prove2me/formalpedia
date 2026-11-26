-- Prove2me | Theorems.Thm_probabilityMeasure_continuous_lintegral
-- name    : probabilityMeasure_continuous_lintegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:58.85482+00:00
-- url     : https://prove2.me/theorems/9c5a180a-a157-4a57-b83a-75ff8763da82
-- title:
--   probability Measure continuous lintegral: probability Measure continuous lintegral
-- statement:
--   Integration of a bounded continuous test function is continuous in the
--       measure, for the topology of weak convergence.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/ProbabilityMeasurePolish.lean#L646-L658
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/ProbabilityMeasurePolish.lean#L646-L658

import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.PiSystem
import Mathlib.MeasureTheory.Measure.GiryMonad
import Definitions.Def_BicausalOT_DescriptiveSetTheory_ProbabilityMeasurePolish
set_option autoImplicit false
open MeasureTheory Topology TopologicalSpace Metric Filter Set
open scoped ENNReal NNReal Classical
noncomputable section
variable {Ω : Type*} [MetricSpace Ω] [SeparableSpace Ω] [CompleteSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]
omit [SeparableSpace Ω] [CompleteSpace Ω]

theorem probabilityMeasure_continuous_lintegral (f : BoundedContinuousFunction Ω ℝ≥0) :
    Continuous fun γ : ProbabilityMeasure Ω =>
      ∫⁻ x, (f x : ℝ≥0∞) ∂(γ : Measure Ω) := by sorry
