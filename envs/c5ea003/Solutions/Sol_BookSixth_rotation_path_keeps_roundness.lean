-- Prove2me | solution 1 for BookSixth.rotation_path_keeps_roundness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-25T18:22:46.582552+00:00
-- url     : https://prove2.me/submissions/57216e34-cb9a-41a9-9de5-0a8a5d3b2e6a

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_rotation_01_preserves_roundness

open scoped BigOperators
open BookSixth

/-- The time-indexed form of `rotation_01_preserves_roundness`.

At time `t` the rotation sweeps the angle `t * θ`, so the accepted one-step result
applies with the angle instantiated to `t * θ`. This is one of the building blocks of
the Chapter 15, Theorem 1 motion, where a round circle must remain round at every
intermediate time and not merely at the endpoint. -/
theorem solution (C : Set Space3) (θ : ℝ) (t : ℝ) (hC : RoundCircle C) :
    RoundCircle
      ((fun x : Space3 => ![Real.cos (t * θ) * x 0 - Real.sin (t * θ) * x 1,
          Real.sin (t * θ) * x 0 + Real.cos (t * θ) * x 1, x 2]) '' C) :=
  BookSixth.rotation_01_preserves_roundness C (t * θ) hC
