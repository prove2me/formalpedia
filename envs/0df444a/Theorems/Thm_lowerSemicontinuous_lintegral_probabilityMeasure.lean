-- Prove2me | Theorems.Thm_lowerSemicontinuous_lintegral_probabilityMeasure
-- name    : lowerSemicontinuous_lintegral_probabilityMeasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:08:32.041406+00:00
-- url     : https://prove2.me/theorems/1e1dfa4c-6798-41de-810d-2aa7ced531e2
-- title:
--   lower Semicontinuous lintegral probability Measure: lower Semicontinuous lintegral probability Measure
-- statement:
--   **Lower semicontinuity of integration on `P(W)`.** For a Polish Borel space `W` and a
--   lower semicontinuous `f : W → ℝ≥0∞`, the map `γ ↦ ∫⁻ x, f x ∂γ` is lower semicontinuous
--   on `ProbabilityMeasure W` with the topology of weak convergence.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/LintegralLsc.lean#L138-L159
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/LintegralLsc.lean#L138-L159

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LintegralLsc
set_option autoImplicit false
open MeasureTheory Filter Set Topology
open scoped ENNReal

theorem lowerSemicontinuous_lintegral_probabilityMeasure
    {W : Type*} [MeasurableSpace W] [TopologicalSpace W] [PolishSpace W] [BorelSpace W]
    {f : W → ℝ≥0∞} (hf : LowerSemicontinuous f) :
    LowerSemicontinuous fun γ : ProbabilityMeasure W => ∫⁻ x, f x ∂(γ : Measure W) := by sorry
