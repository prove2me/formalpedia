-- Prove2me | Theorems.Thm_ex_2_1_2_binary_sequences_no_nat_injection
-- name    : ex_2_1_2_binary_sequences_no_nat_injection
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T18:41:27.191652+00:00
-- url     : https://prove2.me/theorems/a251ed79-101f-4fc5-aba0-ee55b5d495d7
-- title:
--   Chapter 2, ex_2_1_2: ex_2_1_2_binary_sequences_no_nat_injection
-- statement:
--   Source theorem `ex_2_1_2_binary_sequences_no_nat_injection` from Chapter 2, module `ex_2_1_2`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/ex_2_1_2.lean

import Definitions.Def_ProbabilityTheory_chapter_02_ex_2_1_2_F000
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Tactic

open scoped Set
open scoped BigOperators

noncomputable section

theorem ex_2_1_2_binary_sequences_no_nat_injection :
    ¬ ∃ enc : (ℕ → Bool) → ℕ, Function.Injective enc := by sorry
