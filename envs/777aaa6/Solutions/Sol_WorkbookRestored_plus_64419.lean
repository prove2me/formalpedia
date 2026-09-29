-- Prove2me | solution 1 for WorkbookRestored.plus_64419
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:12.25824+00:00
-- url     : https://prove2.me/submissions/7646dbe8-5ba2-4958-94c8-7c788d3f82f4

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_64419.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a b c d : ℝ) : cos (a + b) * sin (a - b) + cos (b + c) * sin (b - c) + cos (c + d) * sin (c - d) + cos (d + a) * sin (d - a) = 0   := by
  have h : ∀ u v : ℝ, cos (u+v)*sin (u-v) = sin u*cos u - sin v*cos v := by
    intro u v
    rw [cos_add,sin_sub]
    linear_combination (cos u*sin u)*(sin_sq_add_cos_sq v) - (cos v*sin v)*(sin_sq_add_cos_sq u)
  rw [h,h,h,h]
  ring
#print axioms solution
