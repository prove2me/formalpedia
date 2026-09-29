-- Prove2me | solution 1 for WorkbookRestored.plus_9318
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:34:58.63629+00:00
-- url     : https://prove2.me/submissions/765320cd-05d9-4c36-86c8-1d0d65a0a0c5

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_9318.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : Real.cos (π / 2) + Real.cos (3 * π / 2) = 0 + 0   := by
  rw [show (3 : ℝ) * π / 2 = π + π / 2 by ring, cos_add]
  norm_num [cos_pi, sin_pi]
#print axioms solution
