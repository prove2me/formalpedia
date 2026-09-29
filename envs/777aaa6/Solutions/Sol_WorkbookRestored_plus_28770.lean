-- Prove2me | solution 1 for WorkbookRestored.plus_28770
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:18:57.11016+00:00
-- url     : https://prove2.me/submissions/65367cae-b07e-4772-bcba-d35022cab54a

/- Adapted from InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_28770. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x ≥ y) : x^x * y^y ≥ x^y * y^x   := by
  simp [rpow_def_of_pos hx, rpow_def_of_pos hy]
  rw [← exp_add, ← exp_add, add_comm]
  refine' exp_le_exp.2 _
  nlinarith [log_le_log (by positivity) hxy]
#print axioms solution
