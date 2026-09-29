-- Prove2me | solution 1 for WorkbookRestored.plus_15750
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:18.344588+00:00
-- url     : https://prove2.me/submissions/105ebd80-b2c8-480a-8435-02c1c1a7c545

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_15750.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) : Real.arccos x + Real.arcsin x = π/2   := by
  rw [add_comm, arcsin_eq_pi_div_two_sub_arccos, sub_add_cancel]
#print axioms solution
