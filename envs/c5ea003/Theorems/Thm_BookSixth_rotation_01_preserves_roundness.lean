-- Prove2me | Theorems.Thm_BookSixth_rotation_01_preserves_roundness
-- name    : BookSixth.rotation_01_preserves_roundness
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-25T16:44:48.620303+00:00
-- url     : https://prove2.me/theorems/c6ef30d4-c446-409d-aa34-03f8d08c572b
-- title:
--   A rotation of the first two coordinates sends a round circle to a round circle
-- statement:
--   Let C be a genuine round circle in R^3 and let theta be a real angle. Rotate R^3 about the third axis, acting as the planar rotation [[cos, -sin], [sin, cos]] on the first two coordinates and fixing the third. Then the image of C is again a genuine round circle. If C has centre c, orthonormal directions u and v and radius r, the image has centre the rotated c, radius r unchanged, and direction pair cos(theta)*u + sin(theta)*v and -sin(theta)*u + cos(theta)*v. Unlike a uniform similarity, a rotation genuinely mixes the two directions, so all three orthonormal equations are re-verified from Real.cos_sq_add_sin_sq. This is the second ingredient of every rigid-motion path used to standardise round circles, after the similarity case.
-- source:
--   Support lemma for BookSixth.perfect_circles_pairwise_unlinked_motion (Chapter 15, Theorem 1 of Aigner-Ziegler, Proofs from THE BOOK, sixth edition).

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.rotation_01_preserves_roundness (C : Set Space3) (θ : ℝ)
    (hC : RoundCircle C) :
    RoundCircle
      ((fun x : Space3 => ![Real.cos θ * x 0 - Real.sin θ * x 1,
          Real.sin θ * x 0 + Real.cos θ * x 1, x 2]) '' C) := by sorry
