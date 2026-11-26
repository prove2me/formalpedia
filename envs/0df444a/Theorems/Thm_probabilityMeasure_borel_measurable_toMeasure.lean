-- Prove2me | Theorems.Thm_probabilityMeasure_borel_measurable_toMeasure
-- name    : probabilityMeasure_borel_measurable_toMeasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:06:59.509915+00:00
-- url     : https://prove2.me/theorems/899caba9-48db-423c-955c-6c1e34503070
-- title:
--   probability Measure borel measurable to Measure: probability Measure borel measurable to Measure
-- statement:
--   **W2**: the coercion from probability measures (Borel σ-algebra of the
--       weak topology) to measures (Giry σ-algebra) is measurable.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/ProbabilityMeasurePolish.lean#L718-L724
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/ProbabilityMeasurePolish.lean#L718-L724

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

theorem probabilityMeasure_borel_measurable_toMeasure :
    @Measurable (ProbabilityMeasure Ω) (Measure Ω)
      (borel (ProbabilityMeasure Ω)) inferInstance
      ((↑) : ProbabilityMeasure Ω → Measure Ω) := by sorry
