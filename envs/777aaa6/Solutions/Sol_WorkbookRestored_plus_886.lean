-- Prove2me | solution 1 for WorkbookRestored.plus_886
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:17:40.627987+00:00
-- url     : https://prove2.me/submissions/e37b9237-cdfa-4d0c-972f-b3ced6a4896c

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_886.
   Draft repair: only required imports and namespaces are restored. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x, sin x = 2 * sin (x / 2) * cos (x / 2)   := by
  intro x
  rw [← Real.sin_two_mul]
  congr 1
  ring
#print axioms solution
