-- Prove2me | Theorems.Thm_isTightMeasureSet_range_of_tendsto
-- name    : isTightMeasureSet_range_of_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:09:00.655809+00:00
-- url     : https://prove2.me/theorems/60b71814-b7a2-4308-8f49-24b509e0121c
-- title:
--   is Tight Measure Set range of tendsto: is Tight Measure Set range of tendsto
-- statement:
--   A convergent sequence of probability measures on a Polish space is a
--       tight family (converse Prokhorov on the compact closure of its range).
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/CouplingsUHC.lean#L29-L48
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/CouplingsUHC.lean#L29-L48

import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsCompact
import Definitions.Def_BicausalOT_DescriptiveSetTheory_ProbabilityMeasurePolish
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
set_option autoImplicit false
open MeasureTheory Set Filter Topology
noncomputable section

theorem isTightMeasureSet_range_of_tendsto {Ω : Type*}
    [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    {γs : ℕ → ProbabilityMeasure Ω} {γ : ProbabilityMeasure Ω}
    (hγ : Tendsto γs atTop (𝓝 γ)) :
    IsTightMeasureSet {((γs n : ProbabilityMeasure Ω) : Measure Ω) | n : ℕ} := by sorry
