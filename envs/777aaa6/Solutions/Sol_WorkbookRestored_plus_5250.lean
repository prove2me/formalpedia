-- Prove2me | solution 1 for WorkbookRestored.plus_5250
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:31:08.398692+00:00
-- url     : https://prove2.me/submissions/54f78f96-90c7-4153-a884-60aaf0c48ad1

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_5250.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a x : ℝ) : Real.sin (a + x) - Real.sin (a - x) = 2 * Real.cos a * Real.sin x   := by
  simp [sin_add, sin_sub, cos_sub]
  ring
#print axioms solution
