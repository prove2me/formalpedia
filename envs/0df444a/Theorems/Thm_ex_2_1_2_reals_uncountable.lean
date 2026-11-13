-- Prove2me | Theorems.Thm_ex_2_1_2_reals_uncountable
-- name    : ex_2_1_2_reals_uncountable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:57:12.246179+00:00
-- url     : https://prove2.me/theorems/8b3e34f0-69db-41c0-96a3-643559064d26
-- title:
--   Chapter 2, ex_2_1_2: ex_2_1_2_reals_uncountable
-- statement:
--   Source theorem `ex_2_1_2_reals_uncountable` from Chapter 2, module `ex_2_1_2`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/ex_2_1_2.lean

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_1_F000
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Tactic

open scoped Set
open scoped BigOperators

noncomputable section

theorem ex_2_1_2_reals_uncountable :
    ¬ IsCountableSet (Set.univ : Set ℝ) := by sorry
