-- Prove2me | solution 1 for WorkbookRestored.plus_162
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:17:34.333864+00:00
-- url     : https://prove2.me/submissions/1ca70226-42a0-4f77-accb-c2ec9fef9cde

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_162.
   Draft repair: only required imports and namespaces are restored. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution  (a b c : ℝ) :
  Real.cos (a + b) * Real.sin b - Real.cos (a + c) * Real.sin c
    = Real.sin (a + b) * Real.cos b - Real.sin (a + c) * Real.cos c   := by
  have hb : Real.sin (a+b) * Real.cos b - Real.cos (a+b) * Real.sin b = Real.sin a := by
    rw [← Real.sin_sub, add_sub_cancel_right]
  have hc : Real.sin (a+c) * Real.cos c - Real.cos (a+c) * Real.sin c = Real.sin a := by
    rw [← Real.sin_sub, add_sub_cancel_right]
  linarith
#print axioms solution
