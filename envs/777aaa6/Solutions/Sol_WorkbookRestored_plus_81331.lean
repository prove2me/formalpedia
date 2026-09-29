-- Prove2me | solution 1 for WorkbookRestored.plus_81331
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:38.272083+00:00
-- url     : https://prove2.me/submissions/2df98363-4e9b-441f-adb5-568091fe4702

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_81331.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (f : ℝ → ℝ) (x : ℝ) : 1 - f x = (9 * exp x + 2) / (12 * exp x + 3) ↔ f x = (3 * exp x + 1) / (12 * exp x + 3)   := by
  constructor <;> intro h <;> field_simp [exp_ne_zero x] at h ⊢ <;> linarith
#print axioms solution
