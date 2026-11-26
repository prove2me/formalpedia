-- Prove2me | Theorems.Thm_probabilityMeasure_borel_measurable_apply
-- name    : probabilityMeasure_borel_measurable_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:03:04.463926+00:00
-- url     : https://prove2.me/theorems/4f3a513b-fc41-4c13-9df7-dde89723d446
-- title:
--   probability Measure borel measurable apply: probability Measure borel measurable apply
-- statement:
--   The measure of any Borel set is a Borel function of the measure
--       (π-λ induction from the closed sets).
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/ProbabilityMeasurePolish.lean#L683-L713
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/ProbabilityMeasurePolish.lean#L683-L713

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

theorem probabilityMeasure_borel_measurable_apply
    {s : Set Ω} (hs : MeasurableSet s) :
    @Measurable (ProbabilityMeasure Ω) ℝ≥0∞
      (borel (ProbabilityMeasure Ω)) inferInstance
      (fun γ => (γ : Measure Ω) s) := by sorry
