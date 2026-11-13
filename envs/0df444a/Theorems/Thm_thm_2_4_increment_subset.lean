-- Prove2me | Theorems.Thm_thm_2_4_increment_subset
-- name    : thm_2_4_increment_subset
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:18:18.251194+00:00
-- url     : https://prove2.me/theorems/5f13972a-7ceb-4de6-b1ff-a9e86dcd766e
-- title:
--   ProbabilityTheory_chapter_02_thm_2_4_F000: thm_2_4_increment_subset
-- statement:
--   Source theorem `thm_2_4_increment_subset` extracted from `ProbabilityTheory.chapter_02.thm_2_4`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_4.lean

import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_4_F000
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_6_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
open MeasureTheory Set
open scoped BigOperators

theorem thm_2_4_increment_subset {Ω : Type*} (A : ℕ → Set Ω) (n : ℕ) :
    thm_2_4_increment A n ⊆ A n := by
  sorry
