-- Prove2me | Theorems.Thm_EuclideanSpace_isBounded_coordinate_rectangle
-- name    : EuclideanSpace.isBounded_coordinate_rectangle
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-30T15:00:55.8863+00:00
-- url     : https://prove2.me/theorems/a1aea1a5-92ff-4e61-a196-05cecf2e7d3b
-- title:
--   Coordinate rectangles are bounded
-- statement:
--   A rectangle with finite coordinate bounds in R^2 is bounded.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Analysis/InnerProductSpace/Box.lean#L9-L10

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace EuclideanSpace

theorem isBounded_coordinate_rectangle (l r a b : ℝ) :
    Bornology.IsBounded {p : EuclideanSpace ℝ (Fin 2) | l ≤ p 0 ∧ p 0 ≤ r ∧ a ≤ p 1 ∧ p 1 ≤ b} := by sorry

end EuclideanSpace
