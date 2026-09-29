-- Prove2me | solution 1 for Erdos180.symmetricQuadratic_eq_bilinear
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:53:25.841023+00:00
-- url     : https://prove2.me/submissions/77bb8ac1-2825-4710-bc68-603cb9530039

import Definitions.Def_erdos180_core4
import Mathlib.Tactic.Ring.Basic

open Erdos180
variable {K : Type*} [CommRing K]

theorem solution
    (a b c x y : K) :
    symmetricQuadratic a b c x y =
      x * (a * x + b * y) + y * (b * x + c * y) := by
  unfold symmetricQuadratic
  ring
