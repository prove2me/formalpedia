-- Prove2me | solution 1 for BookSixth.image_comp_preserves_roundness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-25T18:09:14.371074+00:00
-- url     : https://prove2.me/submissions/6246b990-70b7-42fd-b9d0-9a3d6c52a14d

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

/-- The image of a round circle under a composition of two maps is round whenever the
intermediate image is round. This is the gluing principle that lets the elementary
lemmas for scaling, translating and rotating be assembled into a whole rigid-motion
path without re-checking the orthonormal equations at each composition. -/
theorem solution (f g : Space3 → Space3) (C : Set Space3)
    (hf : RoundCircle (f '' (g '' C))) :
    RoundCircle ((f ∘ g) '' C) := by
  rw [Set.image_comp]
  exact hf
