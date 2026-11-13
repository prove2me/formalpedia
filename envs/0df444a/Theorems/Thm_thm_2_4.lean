-- Prove2me | Theorems.Thm_thm_2_4
-- name    : thm_2_4
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:20:55.507405+00:00
-- url     : https://prove2.me/theorems/7504687f-ca6a-4818-80a7-c8243ee7f327
-- title:
--   Chapter 2, thm_2_4: thm_2_4
-- statement:
--   Source theorem `thm_2_4` from Chapter 2, module `thm_2_4`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_4.lean

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_6_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

open MeasureTheory Set
open scoped BigOperators

theorem thm_2_4 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A : ℕ → Set Ω)
    (hA : SetSeqIncreasing A) (hAmeas : ∀ n, MeasurableSet (A n)) :
    μ (⋃ i, A i) = ⨆ i, μ (A i) := by sorry
