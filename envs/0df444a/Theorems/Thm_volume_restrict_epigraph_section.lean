-- Prove2me | Theorems.Thm_volume_restrict_epigraph_section
-- name    : volume_restrict_epigraph_section
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:03:18.848537+00:00
-- url     : https://prove2.me/theorems/76375b57-3bca-55ec-9a51-80c3a32e45bf
-- title:
--   volume restrict epigraph section: volume restrict epigraph section
-- statement:
--   The volume restrict epigraph section construction uses the volume restrict epigraph section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/KernelIntegral.lean#L190-L220
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/KernelIntegral.lean#L190-L220

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

theorem volume_restrict_epigraph_section (t : ℝ≥0∞) (n : ℕ) :
    volume.restrict (Icc (0 : ℝ) n) {b : ℝ | t ≤ ENNReal.ofReal b}
      = (n : ℝ≥0∞) - min t (n : ℝ≥0∞) := by sorry
