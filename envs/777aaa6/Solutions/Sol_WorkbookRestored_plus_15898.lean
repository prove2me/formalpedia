-- Prove2me | solution 1 for WorkbookRestored.plus_15898
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:20.113979+00:00
-- url     : https://prove2.me/submissions/13c17be4-901b-45c1-a215-cc67471f31b8

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_15898.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (α : ℝ) : -1 ≤ Real.cos α ∧ Real.cos α ≤ 1   := by
  constructor <;> linarith [Real.cos_le_one α, Real.neg_one_le_cos α]
#print axioms solution
