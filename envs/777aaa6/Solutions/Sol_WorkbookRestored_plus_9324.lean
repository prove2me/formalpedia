-- Prove2me | solution 1 for WorkbookRestored.plus_9324
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:34:59.375659+00:00
-- url     : https://prove2.me/submissions/725a1f54-e66d-4df4-9e90-cd00dbc294e5

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_9324.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a : ℝ) (h : sin a + cos a = 1/5) : sin a ^ 3 + cos a ^ 3 = 37/125   := by
  have hs := congrArg (fun t : ℝ => t^2) h
  have hab : sin a * cos a = -12/25 := by
    nlinarith [sin_sq_add_cos_sq a]
  calc
    sin a ^ 3 + cos a ^ 3 = (sin a + cos a)^3 - 3 * (sin a * cos a) * (sin a + cos a) := by ring
    _ = 37/125 := by rw [h, hab]; norm_num
#print axioms solution
