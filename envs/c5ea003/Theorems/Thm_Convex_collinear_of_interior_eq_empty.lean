-- Prove2me | Theorems.Thm_Convex_collinear_of_interior_eq_empty
-- name    : Convex.collinear_of_interior_eq_empty
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-30T17:20:16.989862+00:00
-- url     : https://prove2.me/theorems/fa8ec52f-859d-46aa-9122-1802db19b535
-- title:
--   Thin convex sets are collinear
-- statement:
--   A convex set with empty interior in dimension at most 2 is collinear: empty case or affine-span dimension count. Drift: Linarith umbrella for nlinarith, core omega.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Convex/Collinear.lean#L7-L10

import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linarith
open Module

namespace Convex

theorem collinear_of_interior_eq_empty {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (hs : Convex ℝ s) (hdim : finrank ℝ E ≤ 2)
    (hint : interior s = ∅) : Collinear ℝ s := by sorry

end Convex
