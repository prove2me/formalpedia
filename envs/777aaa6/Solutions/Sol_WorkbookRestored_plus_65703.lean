-- Prove2me | solution 1 for WorkbookRestored.plus_65703
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:14.360974+00:00
-- url     : https://prove2.me/submissions/1c582bc3-351a-4cee-bd36-40bdf323796d

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_65703.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (α β γ : ℝ) (h : α = π - (β + γ)) : sin α = sin (β + γ)   := by
  simp [h, sin_add, sin_sub]
#print axioms solution
