-- Prove2me | solution 1 for BookSixth.shrinking_similarity_scale_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T05:26:02.316293+00:00
-- url     : https://prove2.me/submissions/fd8237c7-3ee1-48e6-8002-2af845146c7b

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem solution (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 < 1 - t := by
  linarith
