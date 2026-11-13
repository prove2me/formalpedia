-- Prove2me | Theorems.Thm_taggedCommonLimit_unique
-- name    : taggedCommonLimit_unique
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T18:42:36.176934+00:00
-- url     : https://prove2.me/theorems/9ad1ac2e-57c2-4841-8829-20c505c7bcd2
-- title:
--   Chapter 1, def_1_2: taggedCommonLimit_unique
-- statement:
--   Source theorem `taggedCommonLimit_unique` from Chapter 1, module `def_1_2`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/def_1_2.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic

open scoped BigOperators Pointwise

noncomputable section

section RS_integral_uniqueness

theorem taggedCommonLimit_unique {a b : ℝ} {f alpha : ℝ → ℝ} {L₁ L₂ : ℝ}
    (h₁ : TaggedCommonLimit a b f alpha L₁)
    (h₂ : TaggedCommonLimit a b f alpha L₂) :
    L₁ = L₂ := by sorry

end RS_integral_uniqueness
