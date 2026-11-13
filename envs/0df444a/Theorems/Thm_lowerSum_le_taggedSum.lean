-- Prove2me | Theorems.Thm_lowerSum_le_taggedSum
-- name    : lowerSum_le_taggedSum
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T22:18:16.884531+00:00
-- url     : https://prove2.me/theorems/bf7f97a7-f965-4bef-ba75-5352198637c7
-- title:
--   ProbabilityTheory_chapter_01_thm_1_2_F008: lowerSum_le_taggedSum
-- statement:
--   Source theorem `lowerSum_le_taggedSum` from `ProbabilityTheory.chapter_01.thm_1_2`. The formal Lean declaration specifies its proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic
open scoped BigOperators Pointwise
open Finset Set
noncomputable section Thm_1_2
namespace DarbouxRS
end DarbouxRS

theorem lowerSum_le_taggedSum {a b : ℝ} {f alpha : ℝ → ℝ}
    (hs : SourceHypotheses a b f alpha)
    (P : Partition a b)
    (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) :
    lowerSum P f alpha ≤ taggedSum P tags f alpha := by
  sorry
end Thm_1_2
