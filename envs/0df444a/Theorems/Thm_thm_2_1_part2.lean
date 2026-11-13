-- Prove2me | Theorems.Thm_thm_2_1_part2
-- name    : thm_2_1_part2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:24:21.498199+00:00
-- url     : https://prove2.me/theorems/ff7a17d3-54ff-4f69-b42a-4dab4030c325
-- title:
--   Chapter 2, thm_2_1: thm_2_1_part2
-- statement:
--   Source theorem `thm_2_1_part2` from Chapter 2, module `thm_2_1`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_1.lean

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_4_F000
import Mathlib.Tactic

open Set

theorem thm_2_1_part2 {Ω : Type*} (E : ℕ → Set Ω) :
  (∀ ω, ω ∈ setLimsup E ↔ ∀ N : ℕ, ∃ n ≥ N, ω ∈ E n) := by sorry
