-- Prove2me | Theorems.Thm_thm_2_4_partial_increment_union_eq
-- name    : thm_2_4_partial_increment_union_eq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:19:19.5444+00:00
-- url     : https://prove2.me/theorems/ed6e7b1e-7805-4968-9d1e-7ced4f90a5cf
-- title:
--   Chapter 2, thm_2_4: thm_2_4_partial_increment_union_eq
-- statement:
--   Source theorem `thm_2_4_partial_increment_union_eq` from Chapter 2, module `thm_2_4`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_4.lean

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_6_F000
import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_4_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

open MeasureTheory Set
open scoped BigOperators

theorem thm_2_4_partial_increment_union_eq {Ω : Type*} {A : ℕ → Set Ω}
    (hA : SetSeqIncreasing A) :
    ∀ n : ℕ, (⋃ i ∈ Set.Iic n, thm_2_4_increment A i) = A n := by sorry
