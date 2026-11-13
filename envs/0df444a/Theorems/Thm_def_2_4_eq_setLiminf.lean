-- Prove2me | Theorems.Thm_def_2_4_eq_setLiminf
-- name    : def_2_4_eq_setLiminf
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:23:33.666461+00:00
-- url     : https://prove2.me/theorems/8930f13b-f842-4cc1-a532-bc144cbc02c2
-- title:
--   ProbabilityTheory_chapter_02_def_2_4_F000: def_2_4_eq_setLiminf
-- statement:
--   Source theorem `def_2_4_eq_setLiminf` extracted from `ProbabilityTheory.chapter_02.def_2_4`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/def_2_4.lean

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_4_F000
import Mathlib.Tactic
open Set

theorem def_2_4_eq_setLiminf {Ω : Type*} (E : ℕ → Set Ω)
    (h : setSeqLimitExists E) :
    def_2_4 E h = setLiminf E := by
  sorry
attribute [simp] def_2_4_eq_setLiminf
