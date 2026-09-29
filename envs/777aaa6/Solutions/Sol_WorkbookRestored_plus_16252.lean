-- Prove2me | solution 1 for WorkbookRestored.plus_16252
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:22.393464+00:00
-- url     : https://prove2.me/submissions/025fe03e-92a4-406a-a87b-bedf88c6172e

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_16252.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a : ℝ) (ha : a > 0) : Real.cosh (Real.log a) = (a^2 + 1) / (2 * a)   := by
  rw [cosh_eq, exp_neg, exp_log ha]
  field_simp <;> ring
#print axioms solution
