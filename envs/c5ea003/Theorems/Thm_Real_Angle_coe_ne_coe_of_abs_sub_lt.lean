-- Prove2me | Theorems.Thm_Real_Angle_coe_ne_coe_of_abs_sub_lt
-- name    : Real.Angle.coe_ne_coe_of_abs_sub_lt
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-30T14:06:09.222476+00:00
-- url     : https://prove2.me/theorems/c73af66a-c23b-4b41-9df2-779207a83c3b
-- title:
--   Close distinct reals give distinct angles
-- statement:
--   If $|x-y|<2\pi$ and $x\ne y$, their angle coercions differ.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Analysis/SpecialFunctions/Angle.lean#L7-L8

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Tactic.Linarith
open Real.Angle

namespace Real.Angle

theorem coe_ne_coe_of_abs_sub_lt {x y : ℝ} (hne : x ≠ y) (h : |x - y| < 2 * Real.pi) : ((x : ℝ) : Real.Angle) ≠ ((y : ℝ) : Real.Angle) := by sorry

end Real.Angle
