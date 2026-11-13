-- Prove2me | Theorems.Thm_thm_2_4_increment_measurable
-- name    : thm_2_4_increment_measurable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:18:56.801137+00:00
-- url     : https://prove2.me/theorems/b0902646-e660-4f28-84e3-bb83a259145b
-- title:
--   ProbabilityTheory_chapter_02_thm_2_4_F000: thm_2_4_increment_measurable
-- statement:
--   Source theorem `thm_2_4_increment_measurable` extracted from `ProbabilityTheory.chapter_02.thm_2_4`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_4.lean

import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_4_F000
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_6_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
open MeasureTheory Set
open scoped BigOperators

theorem thm_2_4_increment_measurable {Ω : Type*} [MeasurableSpace Ω]
    {A : ℕ → Set Ω} (hAmeas : ∀ n, MeasurableSet (A n)) :
    ∀ n, MeasurableSet (thm_2_4_increment A n) := by
  sorry
