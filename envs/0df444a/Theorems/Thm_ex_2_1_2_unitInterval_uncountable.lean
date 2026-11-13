-- Prove2me | Theorems.Thm_ex_2_1_2_unitInterval_uncountable
-- name    : ex_2_1_2_unitInterval_uncountable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:56:58.892825+00:00
-- url     : https://prove2.me/theorems/3ba9772f-82a4-46f7-b27d-670914dfe94a
-- title:
--   Chapter 2, ex_2_1_2
-- statement:
--   Supporting Lean declarations for Chapter 2, source module `ex_2_1_2`: `ex_2_1_2_unitInterval_uncountable`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/ex_2_1_2.lean

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_1_F000
import Definitions.Def_ProbabilityTheory_chapter_02_ex_2_1_2_F000
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Tactic

open scoped Set
open scoped BigOperators

noncomputable section

/-- # Example 2.1.2 The unit interval is uncountable -/
theorem ex_2_1_2_unitInterval_uncountable :
    ¬ IsCountableSet (Set.Icc (0 : ℝ) 1) := by
  sorry
