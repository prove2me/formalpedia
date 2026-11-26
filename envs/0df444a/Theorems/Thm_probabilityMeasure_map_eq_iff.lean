-- Prove2me | Theorems.Thm_probabilityMeasure_map_eq_iff
-- name    : probabilityMeasure_map_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:05:16.216049+00:00
-- url     : https://prove2.me/theorems/f874158d-16c8-53b0-bd9c-53e6f5062cef
-- title:
--   probability Measure map eq iff: probability Measure map eq iff
-- statement:
--   A marginal-type constraint on a `ProbabilityMeasure` can be stated equivalently via
--   `ProbabilityMeasure.map` or via `Measure.map` on the underlying measures.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/CouplingsCompact.lean#L51-L60
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/CouplingsCompact.lean#L51-L60

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsCompact
set_option autoImplicit false
open MeasureTheory Topology
noncomputable section
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

theorem probabilityMeasure_map_eq_iff (γ : ProbabilityMeasure Ω) (μ : ProbabilityMeasure Ω')
    {f : Ω → Ω'} (hf : Measurable f) :
    γ.map hf.aemeasurable = μ ↔ (γ : Measure Ω).map f = (μ : Measure Ω') := by sorry
