-- Prove2me | Theorems.Thm_lintegral_lowerSemianalytic
-- name    : lintegral_lowerSemianalytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:06:27.909724+00:00
-- url     : https://prove2.me/theorems/75f4288b-037b-4d3e-9b0b-46f7ba13eafb
-- title:
--   lintegral lower Semianalytic: lintegral lower Semianalytic
-- statement:
--   **Bertsekas–Shreve, Proposition 7.48** (formerly an axiom, now proved):
--       integration of a lower semianalytic function along a Borel-measurable
--       stochastic kernel is lower semianalytic.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/KernelIntegral.lean#L283-L464
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/KernelIntegral.lean#L283-L464

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
variable {X Y : Type*}
  [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]

theorem lintegral_lowerSemianalytic
    {f : X × Y → ℝ≥0∞} (hf : IsLowerSemianalytic (X := X × Y) f)
    {κ : X → Measure Y} (hκ : Measurable κ)
    (hκp : ∀ x, IsProbabilityMeasure (κ x)) :
    IsLowerSemianalytic (fun x => ∫⁻ y, f (x, y) ∂(κ x)) := by sorry
