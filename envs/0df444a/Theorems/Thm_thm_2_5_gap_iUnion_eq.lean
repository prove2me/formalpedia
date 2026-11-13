-- Prove2me | Theorems.Thm_thm_2_5_gap_iUnion_eq
-- name    : thm_2_5_gap_iUnion_eq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:53:17.393235+00:00
-- url     : https://prove2.me/theorems/f5084446-2d98-4746-b441-cc4bd138fbf5
-- title:
--   Source theorem: thm_2_5_gap_iUnion_eq
-- statement:
--   Source theorem extracted from ProbabilityTheory.chapter_02.thm_2_5, with its proposition and original proof recorded separately.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_5.lean

import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_5_F000
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_6_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
open MeasureTheory Set

theorem thm_2_5_gap_iUnion_eq {Ω : Type*} (A : ℕ → Set Ω) :
    (⋃ i, thm_2_5_gap A i) = A 0 \ ⋂ i, A i := by
  sorry
