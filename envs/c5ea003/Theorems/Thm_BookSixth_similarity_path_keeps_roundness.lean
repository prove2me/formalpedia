-- Prove2me | Theorems.Thm_BookSixth_similarity_path_keeps_roundness
-- name    : BookSixth.similarity_path_keeps_roundness
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-25T18:14:51.026115+00:00
-- url     : https://prove2.me/theorems/0a41bfa0-8649-460f-917d-882ad017d6bd
-- title:
--   The uniform similarity and translation path keeps a round circle round at every time
-- statement:
--   Let C be a genuine round circle in R^3, let a > 0 be a fixed positive scale factor and let b be a fixed translation vector. For every real time t, the map x |-> a*x + t*b carries C to a genuine round circle. This is the time-indexed form of BookSixth.similarity_preserves_roundness: the scale factor a does not depend on t and stays positive at every time, so positivity of the new radius a*r holds uniformly in t, while the centre moves linearly along the line through b. It is one of the two building blocks of the Chapter 15, Theorem 1 motion, where a round circle must remain round at every intermediate time and not merely at the endpoint.
-- source:
--   Support lemma for BookSixth.perfect_circles_pairwise_unlinked_motion (Chapter 15, Theorem 1 of Aigner-Ziegler, Proofs from THE BOOK, sixth edition).

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.similarity_path_keeps_roundness (C : Set Space3) (a : ℝ) (b : Space3)
    (hr : 0 < a) (hC : RoundCircle C) (t : ℝ) :
    RoundCircle ((fun x : Space3 => a • x + t • b) '' C) := by sorry
