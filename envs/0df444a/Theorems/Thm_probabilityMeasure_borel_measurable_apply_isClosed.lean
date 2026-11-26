-- Prove2me | Theorems.Thm_probabilityMeasure_borel_measurable_apply_isClosed
-- name    : probabilityMeasure_borel_measurable_apply_isClosed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:58.833259+00:00
-- url     : https://prove2.me/theorems/e54da427-bbfd-598b-ac6e-ed0dd7087b82
-- title:
--   probability Measure borel measurable apply is Closed: probability Measure borel measurable apply is Closed
-- statement:
--   The measure of a closed set is a Borel function of the measure.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/ProbabilityMeasurePolish.lean#L662-L678
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/ProbabilityMeasurePolish.lean#L662-L678

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

theorem probabilityMeasure_borel_measurable_apply_isClosed
    {F : Set Ω} (hF : IsClosed F) :
    @Measurable (ProbabilityMeasure Ω) ℝ≥0∞
      (borel (ProbabilityMeasure Ω)) inferInstance
      (fun γ => (γ : Measure Ω) F) := by sorry
