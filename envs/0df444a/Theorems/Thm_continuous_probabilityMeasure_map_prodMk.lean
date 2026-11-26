-- Prove2me | Theorems.Thm_continuous_probabilityMeasure_map_prodMk
-- name    : continuous_probabilityMeasure_map_prodMk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:09:40.168734+00:00
-- url     : https://prove2.me/theorems/3d3a5fde-bf1c-4160-91da-1134a63cc334
-- title:
--   continuous probability Measure map prod Mk: continuous probability Measure map prod Mk
-- statement:
--   **Joint continuity of the pairing** `(x, γ) ↦ γ.map (Prod.mk x)` from
--       `H × P(W)` to `P(H × W)` (weak topologies, Polish spaces).
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/LscIntegral.lean#L36-L74
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/LscIntegral.lean#L36-L74

import Definitions.Def_BicausalOT_DescriptiveSetTheory_LintegralLsc
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LscIntegral
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
variable {H W : Type*}
  [TopologicalSpace H] [PolishSpace H] [MeasurableSpace H] [BorelSpace H]
  [TopologicalSpace W] [PolishSpace W] [MeasurableSpace W] [BorelSpace W]

theorem continuous_probabilityMeasure_map_prodMk :
    Continuous (fun p : H × ProbabilityMeasure W =>
      ProbabilityMeasure.map p.2
        (measurable_prodMk_left (x := p.1)).aemeasurable) := by sorry
