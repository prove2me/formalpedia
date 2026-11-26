-- Prove2me | Theorems.Thm_iInf_fiber_lt
-- name    : iInf_fiber_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:06:32.010738+00:00
-- url     : https://prove2.me/theorems/a9058500-86a4-5387-bd9a-a5e9134249bc
-- title:
--   i Inf fiber lt: i Inf fiber lt
-- statement:
--   Any value strictly above the fiber infimum is beaten by some element
--       of the fiber.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/EpsOptimalSelection.lean#L36-L43
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/EpsOptimalSelection.lean#L36-L43

import Definitions.Def_BicausalOT_DescriptiveSetTheory_Tree
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Definitions.Def_BicausalOT_DescriptiveSetTheory_EpsOptimalSelection
set_option autoImplicit false
open MeasureTheory Set ENNReal
open scoped Classical
noncomputable section
variable {H E : Type*} [TopologicalSpace H] [TopologicalSpace E]
omit [TopologicalSpace H] [TopologicalSpace E]

theorem iInf_fiber_lt {Γ : Set (H × E)} {F : H × E → ℝ≥0∞} {h : H}
    {q : ℝ≥0∞} (hlt : (⨅ (e : E) (_ : (h, e) ∈ Γ), F (h, e)) < q) :
    ∃ e : E, (h, e) ∈ Γ ∧ F (h, e) < q := by sorry
