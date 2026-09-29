-- Prove2me | solution 1 for WorkbookRestored.plus_33683
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:44.754885+00:00
-- url     : https://prove2.me/submissions/f9d800ad-2d88-4f10-bc1a-cdd70e3a4e24

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_33683.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (A B C : ℝ) : (sin A + sin B + sin C) ^ 2 ≤ 3 * (sin A ^ 2 + sin B ^ 2 + sin C ^ 2)   := by
  linarith [sq_nonneg (sin A - sin B), sq_nonneg (sin B - sin C), sq_nonneg (sin C - sin A)]
#print axioms solution
