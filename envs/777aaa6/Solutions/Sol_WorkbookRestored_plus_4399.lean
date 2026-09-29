-- Prove2me | solution 1 for WorkbookRestored.plus_4399
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:31:02.299818+00:00
-- url     : https://prove2.me/submissions/cc0cc070-dc4a-4ad6-8c6f-d04065340ab1

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_4399.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a : ℝ) : Real.cos (3 * a) = 4 * (Real.cos a)^3 - 3 * Real.cos a   := by
  rw [Real.cos_three_mul]
#print axioms solution
