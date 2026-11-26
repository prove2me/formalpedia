-- Prove2me | Theorems.Thm_borel_le_analyticMeasurableSpace
-- name    : borel_le_analyticMeasurableSpace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:00:58.876047+00:00
-- url     : https://prove2.me/theorems/8faf7262-ca24-4bfe-b9c3-235c5960ff25
-- title:
--   borel le analytic Measurable Space: borel le analytic Measurable Space
-- statement:
--   The borel le analytic Measurable Space construction uses the borel le analytic Measurable Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/AnalyticSigmaAlgebra.lean#L35-L38
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/AnalyticSigmaAlgebra.lean#L35-L38

import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSigmaAlgebra
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
variable {X : Type*} [TopologicalSpace X]

theorem borel_le_analyticMeasurableSpace
    [PolishSpace X] [MeasurableSpace X] [BorelSpace X] :
    ‹MeasurableSpace X› ≤ analyticMeasurableSpace X := by sorry
