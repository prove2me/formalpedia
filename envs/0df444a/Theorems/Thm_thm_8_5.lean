-- Prove2me | Theorems.Thm_thm_8_5
-- name    : thm_8_5
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T18:44:37.496377+00:00
-- url     : https://prove2.me/theorems/01d6eb17-6de4-4acd-ba76-d5d542077fe7
-- title:
--   Chapter 8, thm_8_5: thm_8_5
-- statement:
--   Source theorem `thm_8_5` from Chapter 8, module `thm_8_5`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_08/thm_8_5.lean

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

open MeasureTheory
open scoped ENNReal

theorem thm_8_5
    {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure α) (Q : Measure β)
    [SigmaFinite P] [SigmaFinite Q]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : α × β → E}
    (hf_meas : AEStronglyMeasurable f (P.prod Q))
    (hfinite :
      ((∫⁻ x, ∫⁻ y, ‖f (x, y)‖ₑ ∂Q ∂P) < ∞) ∨
      ((∫⁻ y, ∫⁻ x, ‖f (x, y)‖ₑ ∂P ∂Q) < ∞) ∨
      ((∫⁻ z, ‖f z‖ₑ ∂(P.prod Q)) < ∞)) :
    Integrable f (P.prod Q) ∧
      Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂Q) P ∧
      Integrable (fun y => ∫ x, ‖f (x, y)‖ ∂P) Q ∧
      (∫ x, ∫ y, f (x, y) ∂Q ∂P = ∫ y, ∫ x, f (x, y) ∂P ∂Q) ∧
      (∫ x, ∫ y, f (x, y) ∂Q ∂P = ∫ z, f z ∂(P.prod Q)) := by sorry
