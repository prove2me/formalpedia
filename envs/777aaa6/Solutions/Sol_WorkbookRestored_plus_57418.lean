-- Prove2me | solution 1 for WorkbookRestored.plus_57418
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:24:59.62698+00:00
-- url     : https://prove2.me/submissions/453f7fe9-aa55-4340-9df7-70301bca672d

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_57418.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (n : ℕ) (hn : 0 < n ∧ n < 9) : Real.cos (n * π / 9) + Real.cos ((9 - n) * π / 9) = 0   := by
  have he : (9-(n:ℝ))*π/9=π-n*π/9 := by ring
  rw [he,cos_pi_sub]
  ring
#print axioms solution
