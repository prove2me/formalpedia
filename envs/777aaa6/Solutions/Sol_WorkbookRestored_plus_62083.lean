-- Prove2me | solution 1 for WorkbookRestored.plus_62083
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:10.773293+00:00
-- url     : https://prove2.me/submissions/a8be01bd-30ed-413b-ac97-e1605347f68d

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_62083.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (α β : ℝ) (h₁ : α + β = π / 4) : cos α * sin α + sin β ^ 2 = cos β * sin β + sin α ^ 2   := by
  have he : α=π/4-β := by linarith
  rw [he,cos_sub,sin_sub,cos_pi_div_four,sin_pi_div_four]
  linear_combination (cos β*sin β-sin β^2)/2 * (sq_sqrt (show (0:ℝ)≤2 by norm_num))
#print axioms solution
