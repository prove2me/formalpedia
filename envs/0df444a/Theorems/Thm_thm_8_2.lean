-- Prove2me | Theorems.Thm_thm_8_2
-- name    : thm_8_2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:51:16.859832+00:00
-- url     : https://prove2.me/theorems/0d2fb78b-1401-4190-afdb-c21a2fa502f9
-- title:
--   Chapter 8, thm_8_2
-- statement:
--   Supporting Lean declarations for Chapter 8, source module `thm_8_2`: `thm_8_2`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_08/thm_8_2.lean

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Tactic

open MeasureTheory

/-- Exported statement for Theorem 8.2: on sigma-finite spaces, the product measure is the
unique measure on the product measurable space agreeing with rectangle masses. -/
theorem thm_8_2
    {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure α) (Q : Measure β)
    [SigmaFinite P] [SigmaFinite Q] :
    ∃! R : Measure (α × β),
      ∀ s : Set α, ∀ t : Set β,
        MeasurableSet s → MeasurableSet t → R (s ×ˢ t) = P s * Q t := by
  sorry
