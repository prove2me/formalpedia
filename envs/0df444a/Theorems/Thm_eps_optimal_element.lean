-- Prove2me | Theorems.Thm_eps_optimal_element
-- name    : eps_optimal_element
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T07:59:36.310807+00:00
-- url     : https://prove2.me/theorems/b4dcc545-ba0c-453d-b552-fab33b3f78b6
-- title:
--   eps optimal element: eps optimal element
-- statement:
--   The eps optimal element construction uses the eps optimal element property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/UpperBound.lean#L16-L28
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/UpperBound.lean#L16-L28

import Definitions.Def_BicausalOT_Defs
import Definitions.Def_BicausalOT_DescriptiveSetTheory_JankovVonNeumann
import Definitions.Def_BicausalOT_UpperBound
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set ENNReal
noncomputable section
variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]
variable (c₀ : X₀ × Y₀ → ENNReal) (c₁ : (X₀ × Y₀) × (X₁ × Y₁) → ENNReal)

theorem eps_optimal_element
    {α : Type*} (S : Set α) (h_ne : S.Nonempty)
    (f : α → ENNReal) (ε : ENNReal) (hε : 0 < ε) :
    ∃ a ∈ S, f a ≤ (⨅ (x : α) (_ : x ∈ S), f x) + ε := by sorry
