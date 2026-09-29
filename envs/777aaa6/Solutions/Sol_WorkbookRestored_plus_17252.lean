-- Prove2me | solution 1 for WorkbookRestored.plus_17252
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:25.367237+00:00
-- url     : https://prove2.me/submissions/af70f515-e495-476f-8e72-28dbc8ccb2d4

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_17252.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (α β : ℝ) : (sin α) ^ 2 - (sin β) ^ 2 = sin (α + β) * sin (α - β)   := by
  simp [sin_add, sin_sub, cos_sub]
  nlinarith [sin_sq_add_cos_sq α, sin_sq_add_cos_sq β]
#print axioms solution
