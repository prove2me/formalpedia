-- Prove2me | Theorems.Thm_thm_8_3
-- name    : thm_8_3
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T18:44:18.683528+00:00
-- url     : https://prove2.me/theorems/aabb2eff-e841-4455-b931-3b72071987c9
-- title:
--   Chapter 8, thm_8_3: thm_8_3
-- statement:
--   Source theorem `thm_8_3` from Chapter 8, module `thm_8_3`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_08/thm_8_3.lean

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

open MeasureTheory

open scoped ENNReal

theorem thm_8_3
    {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure α) (Q : Measure β)
    [SigmaFinite P] [SigmaFinite Q]
    {f : α × β → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ x, ∫⁻ y, f (x, y) ∂Q ∂P)
      = ∫⁻ y, ∫⁻ x, f (x, y) ∂P ∂Q ∧
    (∫⁻ x, ∫⁻ y, f (x, y) ∂Q ∂P)
      = ∫⁻ z, f z ∂(P.prod Q) := by sorry
