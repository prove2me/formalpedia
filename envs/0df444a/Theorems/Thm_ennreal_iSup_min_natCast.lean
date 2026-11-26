-- Prove2me | Theorems.Thm_ennreal_iSup_min_natCast
-- name    : ennreal_iSup_min_natCast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:03:14.893179+00:00
-- url     : https://prove2.me/theorems/dce68653-6633-5007-b732-82f10188d880
-- title:
--   ennreal i Sup min nat Cast: ennreal i Sup min nat Cast
-- statement:
--   The ennreal i Sup min nat Cast construction uses the ennreal i Sup min nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/KernelIntegral.lean#L90-L99
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/KernelIntegral.lean#L90-L99

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

theorem ennreal_iSup_min_natCast (a : ℝ≥0∞) : ⨆ n : ℕ, min a (n : ℝ≥0∞) = a := by sorry
