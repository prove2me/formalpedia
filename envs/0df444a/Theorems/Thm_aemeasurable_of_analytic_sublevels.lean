-- Prove2me | Theorems.Thm_aemeasurable_of_analytic_sublevels
-- name    : aemeasurable_of_analytic_sublevels
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:03:15.526258+00:00
-- url     : https://prove2.me/theorems/eb98d375-0e1f-56b8-b1ca-c07aea325dd8
-- title:
--   aemeasurable of analytic sublevels: aemeasurable of analytic sublevels
-- statement:
--   The aemeasurable of analytic sublevels construction uses the aemeasurable of analytic sublevels property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/KernelIntegral.lean#L106-L131
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/KernelIntegral.lean#L106-L131

import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LowerSemianalytic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
set_option autoImplicit false
open Set Topology MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal
noncomputable section

theorem aemeasurable_of_analytic_sublevels
    {V : Type*} [TopologicalSpace V] [PolishSpace V]
    [MeasurableSpace V] [BorelSpace V] {g : V → ℝ≥0∞}
    (hg : ∀ c, AnalyticSet {v | g v < c})
    (μ : Measure V) [IsFiniteMeasure μ] :
    AEMeasurable g μ := by sorry
