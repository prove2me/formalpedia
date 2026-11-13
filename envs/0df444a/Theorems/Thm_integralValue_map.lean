-- Prove2me | Theorems.Thm_integralValue_map
-- name    : integralValue_map
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:03:29.945391+00:00
-- url     : https://prove2.me/theorems/4b4732a4-4651-4ae8-9a03-034def789602
-- title:
--   Chapter 6, def_6_2: integralValue_map
-- statement:
--   Source theorem `integralValue_map` from Chapter 6, module `def_6_2`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/def_6_2.lean

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F000
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Tactic

open MeasureTheory
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

theorem integralValue_map (μ : Measure Ω) {β : Type*}
    (g : β → EReal) (f : SimpleFunc Ω β) :
    simpleFunctionIntegralValue μ (f.map g) =
      ∑ x ∈ f.range, g x * (μ (f ⁻¹' {x}) : EReal) := by sorry
