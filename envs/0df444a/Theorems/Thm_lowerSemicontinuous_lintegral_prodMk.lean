-- Prove2me | Theorems.Thm_lowerSemicontinuous_lintegral_prodMk
-- name    : lowerSemicontinuous_lintegral_prodMk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:14:34.788077+00:00
-- url     : https://prove2.me/theorems/f01e5521-6423-4c55-ae70-2f8aa1842a27
-- title:
--   lower Semicontinuous lintegral prod Mk: lower Semicontinuous lintegral prod Mk
-- statement:
--   **Joint lower semicontinuity of the integral pairing.** For jointly
--       lower semicontinuous `f : H × W → ℝ≥0∞`, the map
--       `(x, γ) ↦ ∫⁻ z, f (x, z) ∂γ` is jointly lower semicontinuous on
--       `H × P(W)`: it is the lsc integral functional on `P(H × W)`
--       (`lowerSemicontinuous_lintegral_probabilityMeasure`) composed with
--       the continuous pairing (J1).
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/LscIntegral.lean#L84-L100
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/LscIntegral.lean#L84-L100

import Definitions.Def_BicausalOT_DescriptiveSetTheory_LintegralLsc
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LscIntegral
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
variable {H W : Type*}
  [TopologicalSpace H] [PolishSpace H] [MeasurableSpace H] [BorelSpace H]
  [TopologicalSpace W] [PolishSpace W] [MeasurableSpace W] [BorelSpace W]

theorem lowerSemicontinuous_lintegral_prodMk
    {f : H × W → ℝ≥0∞} (hf : LowerSemicontinuous f) :
    LowerSemicontinuous (fun p : H × ProbabilityMeasure W =>
      ∫⁻ z, f (p.1, z) ∂(p.2 : Measure W)) := by sorry
