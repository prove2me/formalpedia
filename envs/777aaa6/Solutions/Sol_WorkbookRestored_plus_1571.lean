-- Prove2me | solution 1 for WorkbookRestored.plus_1571
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:17:43.608396+00:00
-- url     : https://prove2.me/submissions/076e4142-f134-479b-99a9-e9ab321cd4bb

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_1571.
   Draft repair: only required imports and namespaces are restored. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a b x : ℝ) : |a * sin x + b * cos x| ≤ Real.sqrt (a ^ 2 + b ^ 2)   := by
  apply Real.abs_le_sqrt
  nlinarith [sq_nonneg (a * cos x - b * sin x), sin_sq_add_cos_sq x]
#print axioms solution
