-- Prove2me | Theorems.Thm_ennreal_le_iff_forall_lt_add_inv
-- name    : ennreal_le_iff_forall_lt_add_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:03:12.211859+00:00
-- url     : https://prove2.me/theorems/d7967401-2a05-5f50-9eee-276d7bf61bfa
-- title:
--   ennreal le iff forall lt add inv: ennreal le iff forall lt add inv
-- statement:
--   The ennreal le iff forall lt add inv construction uses the ennreal le iff forall lt add inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/KernelIntegral.lean#L74-L88
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/KernelIntegral.lean#L74-L88

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

theorem ennreal_le_iff_forall_lt_add_inv {a q : ℝ≥0∞} (hq : q ≠ ∞) :
    a ≤ q ↔ ∀ k : ℕ, a < q + ((k : ℝ≥0∞) + 1)⁻¹ := by sorry
