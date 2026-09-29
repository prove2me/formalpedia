-- Prove2me | solution 1 for WorkbookRestored.plus_31096
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:34.058263+00:00
-- url     : https://prove2.me/submissions/9cb943a3-96c2-434f-96b5-9723d2b66674

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_31096.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (A B C : ℝ) : Real.cos (A - B) + Real.cos (B - C) + Real.cos (C - A) ≤ 3   := by
  linarith [cos_le_one (A - B), cos_le_one (B - C), cos_le_one (C - A)]
#print axioms solution
