-- Prove2me | Theorems.Thm_def_2_4_eq_setLimsup
-- name    : def_2_4_eq_setLimsup
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:23:47.559195+00:00
-- url     : https://prove2.me/theorems/6bfb11d7-e445-4ea7-b3bd-3b324d4f6e00
-- title:
--   ProbabilityTheory_chapter_02_def_2_4_F000: def_2_4_eq_setLimsup
-- statement:
--   Source theorem `def_2_4_eq_setLimsup` extracted from `ProbabilityTheory.chapter_02.def_2_4`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/def_2_4.lean

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_4_F000
import Mathlib.Tactic
open Set

theorem def_2_4_eq_setLimsup {Ω : Type*} (E : ℕ → Set Ω)
    (h : setSeqLimitExists E) :
    def_2_4 E h = setLimsup E := by
  sorry
