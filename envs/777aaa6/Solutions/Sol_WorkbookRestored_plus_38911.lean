-- Prove2me | solution 1 for WorkbookRestored.plus_38911
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:37:13.707653+00:00
-- url     : https://prove2.me/submissions/76208e58-ae95-4a7d-b478-f1ced3ed0e40

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_38911.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (m : ℝ) : (1 : ℝ) ^ m = 1   := by
  exact Real.one_rpow m
#print axioms solution
