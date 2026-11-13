-- Prove2me | Theorems.Thm_taggedSum_le_upperSum
-- name    : taggedSum_le_upperSum
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T22:18:32.007602+00:00
-- url     : https://prove2.me/theorems/577d5128-221c-4840-930c-668649bef901
-- title:
--   ProbabilityTheory_chapter_01_thm_1_2_F008: taggedSum_le_upperSum
-- statement:
--   Source theorem `taggedSum_le_upperSum` from `ProbabilityTheory.chapter_01.thm_1_2`. The formal Lean declaration specifies its proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic
open scoped BigOperators Pointwise
open Finset Set
noncomputable section Thm_1_2
namespace DarbouxRS
end DarbouxRS

theorem taggedSum_le_upperSum {a b : ℝ} {f alpha : ℝ → ℝ}
    (hs : SourceHypotheses a b f alpha)
    (P : Partition a b)
    (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) :
    taggedSum P tags f alpha ≤ upperSum P f alpha := by
  sorry
end Thm_1_2
