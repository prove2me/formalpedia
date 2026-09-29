-- Prove2me | solution 1 for WorkbookRestored.plus_4590
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:31:03.0615+00:00
-- url     : https://prove2.me/submissions/e347bcd8-4421-4491-9b13-3b158e282d64

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_4590.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : 2 * Real.cos (Real.pi / 4) = Real.sqrt 2   := by
  rw [Real.cos_pi_div_four]
  ring
#print axioms solution
