-- Prove2me | solution 1 for WorkbookRestored.plus_28301
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:30.322427+00:00
-- url     : https://prove2.me/submissions/f679fa2b-3a5a-4955-a5be-a7f0f2b739e0

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_28301.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (θ : ℝ) : Real.cos θ + Real.cos (θ + (2 * Real.pi / 3)) + Real.cos (θ + (4 * Real.pi / 3)) = 0   := by
  simp [cos_add, cos_sub, add_assoc, add_comm, add_left_comm]
  rw [show (2 * π / 3 : ℝ) = π - π / 3 by ring_nf, show (4 * π / 3 : ℝ) = π + π / 3 by ring_nf]
  simp [cos_add, cos_sub, sin_add, sin_sub]
  ring_nf
#print axioms solution
