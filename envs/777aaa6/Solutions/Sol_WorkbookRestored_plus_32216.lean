-- Prove2me | solution 1 for WorkbookRestored.plus_32216
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:38.239372+00:00
-- url     : https://prove2.me/submissions/8126ae69-d238-436c-bc80-b14a4e1fbe29

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_32216.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution {a b c : ℝ} : (Real.cos (a + b + c) + Real.cos (a + b - c) + Real.cos (a + c - b) + Real.cos (b + c - a)) = 4 * Real.cos a * Real.cos b * Real.cos c   := by
  simp [cos_add, cos_sub, sin_add, sin_sub]
  ring_nf
#print axioms solution
