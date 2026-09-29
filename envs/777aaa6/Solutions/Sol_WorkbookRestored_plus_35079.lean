-- Prove2me | solution 1 for WorkbookRestored.plus_35079
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:49.53646+00:00
-- url     : https://prove2.me/submissions/a992370f-4b69-4841-b387-553e027af80b

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_35079.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : cos (π / 7) - cos (5 * π / 7) = cos (π / 7) - cos (3 * π / 7) + cos (2 * π / 7) - cos (4 * π / 7)   := by
  have h1 : (π / 7 : ℝ) = π / 7 := by norm_num
  have h2 : (5 * π / 7 : ℝ) = π - 2 * π / 7 := by ring
  have h3 : (3 * π / 7 : ℝ) = π - 4 * π / 7 := by ring
  simp [h1, h2, h3, cos_add, cos_sub]
  linarith [cos_add (π / 7) (2 * π / 7), cos_add (π / 7) (4 * π / 7)]
#print axioms solution
