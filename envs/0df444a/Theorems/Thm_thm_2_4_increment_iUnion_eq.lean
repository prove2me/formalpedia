-- Prove2me | Theorems.Thm_thm_2_4_increment_iUnion_eq
-- name    : thm_2_4_increment_iUnion_eq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:19:36.356078+00:00
-- url     : https://prove2.me/theorems/f9f3fccb-ac16-46cb-9e48-62f630a62ba3
-- title:
--   02_thm_2_4: thm_2_4_increment_iUnion_eq
-- statement:
--   Original source theorem `thm_2_4_increment_iUnion_eq` in the chapter module. The formal Lean declaration below is the authoritative proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_4.lean

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_6_F000
import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_4_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
open MeasureTheory Set
open scoped BigOperators

theorem thm_2_4_increment_iUnion_eq {Ω : Type*} {A : ℕ → Set Ω}
    (hA : SetSeqIncreasing A) :
    (⋃ i, thm_2_4_increment A i) = ⋃ i, A i := by
  sorry
