-- Prove2me | solution 1 for WorkbookRestored.plus_52577
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:24:49.992286+00:00
-- url     : https://prove2.me/submissions/128f85a6-d75a-4c61-94d6-8daafa89686a

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_52577.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ n : ℤ, cos ((2 * n + 1) * π / 2) = 0   := by
  intro n
  have h : (2 * n + 1) * π / 2 = n * π + π / 2 := by ring
  simp [h,cos_add]
#print axioms solution
