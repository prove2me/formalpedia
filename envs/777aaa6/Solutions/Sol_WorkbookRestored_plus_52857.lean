-- Prove2me | solution 1 for WorkbookRestored.plus_52857
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:49:29.848843+00:00
-- url     : https://prove2.me/submissions/c854e773-2ff5-4946-963a-4095c91c007e

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_52857.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (b : ℝ) (hb : 1 < b) : ∀ x y : ℝ, x < y → b^x < b^y   := by
  intro x y hxy
  exact Real.rpow_lt_rpow_of_exponent_lt hb hxy
#print axioms solution
