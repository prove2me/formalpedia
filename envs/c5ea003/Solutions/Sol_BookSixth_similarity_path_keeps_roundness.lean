-- Prove2me | solution 1 for BookSixth.similarity_path_keeps_roundness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-25T18:15:35.611621+00:00
-- url     : https://prove2.me/submissions/62aa2e9e-53db-4440-b65f-3c4ad2ab241d

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_similarity_preserves_roundness

open scoped BigOperators
open BookSixth

/-- The time-indexed form of `similarity_preserves_roundness`.

The scale factor `a` is independent of `t` and stays positive at every time, so the
new radius `a * r` is positive uniformly in `t` while the centre travels along the
line through `b`. This is one of the building blocks of the Chapter 15, Theorem 1
motion, where a round circle must remain round at every intermediate time and not
merely at the endpoint. -/
theorem solution (C : Set Space3) (a : ℝ) (b : Space3) (hr : 0 < a)
    (hC : RoundCircle C) (t : ℝ) :
    RoundCircle ((fun x : Space3 => a • x + t • b) '' C) :=
  BookSixth.similarity_preserves_roundness C a (t • b) hr hC
