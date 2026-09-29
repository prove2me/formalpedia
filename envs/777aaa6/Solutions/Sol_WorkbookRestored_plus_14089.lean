-- Prove2me | solution 1 for WorkbookRestored.plus_14089
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:12.014801+00:00
-- url     : https://prove2.me/submissions/74fed492-f116-4527-9ad7-9c96fcfff39d

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_14089.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (α β : ℝ) : 2 * sin α ^ 2 + 2 * sin β ^ 2 + 2 ≥ 2 * sin α + 2 * sin β + 2 * sin α * sin β   := by
  nlinarith [sq_nonneg (sin α - sin β), sq_nonneg (sin α - 1), sq_nonneg (sin β - 1)]
#print axioms solution
