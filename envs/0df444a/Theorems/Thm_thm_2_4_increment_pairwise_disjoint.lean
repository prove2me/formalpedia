-- Prove2me | Theorems.Thm_thm_2_4_increment_pairwise_disjoint
-- name    : thm_2_4_increment_pairwise_disjoint
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:18:41.922188+00:00
-- url     : https://prove2.me/theorems/1f74dbb1-93da-47dc-96de-ab3426458d37
-- title:
--   ProbabilityTheory_chapter_02_thm_2_4_F000: thm_2_4_increment_pairwise_disjoint
-- statement:
--   Source theorem `thm_2_4_increment_pairwise_disjoint` extracted from `ProbabilityTheory.chapter_02.thm_2_4`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_4.lean

import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_4_F000
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_6_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
open MeasureTheory Set
open scoped BigOperators

theorem thm_2_4_increment_pairwise_disjoint {Ω : Type*} {A : ℕ → Set Ω}
    (hA : SetSeqIncreasing A) :
    Pairwise (fun i j => Disjoint (thm_2_4_increment A i) (thm_2_4_increment A j)) := by
  sorry
