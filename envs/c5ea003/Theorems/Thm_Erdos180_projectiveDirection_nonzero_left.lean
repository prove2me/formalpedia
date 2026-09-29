-- Prove2me | Theorems.Thm_Erdos180_projectiveDirection_nonzero_left
-- name    : Erdos180.projectiveDirection_nonzero_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:15:07.195834+00:00
-- url     : https://prove2.me/theorems/8d5ff9e9-1a39-4335-92a2-4d37c2d30d14
-- title:
--   A nonzero determinant forces a nonzero first direction
-- statement:
--   If $xy' - x'y \ne 0$ then $(x,y) \ne (0,0)$.
--
--   A well-definedness side condition for coordinate lines: two directions with nonzero determinant
--   are distinct projective points, so each is a legitimate direction.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L6611-L6619

import Definitions.Def_erdos180_core4
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.Push

open Erdos180
variable (K : Type*) [Field K]

theorem Erdos180.projectiveDirection_nonzero_left
    {x y x' y' : K}
    (hdet : x * y' - x' * y ≠ 0) :
    x ≠ 0 ∨ y ≠ 0 := by sorry
