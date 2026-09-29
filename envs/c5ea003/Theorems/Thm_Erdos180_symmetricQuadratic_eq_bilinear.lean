-- Prove2me | Theorems.Thm_Erdos180_symmetricQuadratic_eq_bilinear
-- name    : Erdos180.symmetricQuadratic_eq_bilinear
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:10:41.421405+00:00
-- url     : https://prove2.me/theorems/6863e2d1-44be-4f0d-9903-0a9fb315035a
-- title:
--   The quadratic form in bilinear coordinates
-- statement:
--   For scalars $a,b,c$ and coordinates $x,y$,
--
--   $$Q_{a,b,c}(x,y) \;=\; x(ax + by) + y(bx + cy).$$
--
--   The identity that lets the condition "two lines of the quadrangle have a common point" be read
--   off as the vanishing of an explicit quadratic form, which is how Proposition 4.2 is verified in
--   characteristic two.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L4051-L4056

import Definitions.Def_erdos180_core4
import Mathlib.Tactic.Ring.Basic

open Erdos180
variable {K : Type*} [CommRing K]

theorem Erdos180.symmetricQuadratic_eq_bilinear
    (a b c x y : K) :
    symmetricQuadratic a b c x y =
      x * (a * x + b * y) + y * (b * x + c * y) := by sorry
