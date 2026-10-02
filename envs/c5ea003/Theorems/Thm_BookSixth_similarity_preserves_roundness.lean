-- Prove2me | Theorems.Thm_BookSixth_similarity_preserves_roundness
-- name    : BookSixth.similarity_preserves_roundness
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-25T16:39:08.529601+00:00
-- url     : https://prove2.me/theorems/050cc58c-fca3-4342-912b-c3ad3825e5ec
-- title:
--   A positive uniform similarity sends a round circle to a round circle
-- statement:
--   Let C be a genuine round circle in R^3, let a > 0 be a scale factor and let b be a translation vector. Then the image of C under x |-> a*x + b is again a genuine round circle. Concretely, if C has centre c, orthonormal directions u and v and radius r, the image has centre a*c + b, the same directions u and v, and radius a*r. Because the direction pair is unchanged, the three orthonormal equations are inherited verbatim and only the positivity of the radius has to be rechecked. This is the algebraic core of every rigid-motion path used to standardise round circles.
-- source:
--   Support lemma for BookSixth.perfect_circles_pairwise_unlinked_motion (Chapter 15, Theorem 1 of Aigner-Ziegler, Proofs from THE BOOK, sixth edition).

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.similarity_preserves_roundness (C : Set Space3) (a : ℝ) (b : Space3)
    (ha : 0 < a) (hC : RoundCircle C) :
    RoundCircle ((fun x : Space3 => a • x + b) '' C) := by sorry
