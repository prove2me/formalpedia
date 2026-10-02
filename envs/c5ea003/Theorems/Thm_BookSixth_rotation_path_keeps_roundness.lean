-- Prove2me | Theorems.Thm_BookSixth_rotation_path_keeps_roundness
-- name    : BookSixth.rotation_path_keeps_roundness
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-25T18:21:59.420207+00:00
-- url     : https://prove2.me/theorems/507dc569-3493-4649-9e0e-77afcdb86191
-- title:
--   The rotation path keeps a round circle round at every time
-- statement:
--   Let C be a genuine round circle in R^3 and let theta be a real angle. For every real time t, rotating the first two coordinates of R^3 by the angle t*theta, while fixing the third coordinate, carries C to a genuine round circle. This is the time-indexed form of BookSixth.rotation_01_preserves_roundness: the angle swept at time t is simply t*theta, so the accepted one-step result applies at every time with the angle instantiated to t*theta. It is one of the building blocks of the Chapter 15, Theorem 1 motion, in which a round circle must remain round at every intermediate time and not merely at the endpoint.
-- source:
--   Support lemma for BookSixth.perfect_circles_pairwise_unlinked_motion (Chapter 15, Theorem 1 of Aigner-Ziegler, Proofs from THE BOOK, sixth edition).

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.rotation_path_keeps_roundness (C : Set Space3) (θ : ℝ) (t : ℝ)
    (hC : RoundCircle C) :
    RoundCircle
      ((fun x : Space3 => ![Real.cos (t * θ) * x 0 - Real.sin (t * θ) * x 1,
          Real.sin (t * θ) * x 0 + Real.cos (t * θ) * x 1, x 2]) '' C) := by sorry
