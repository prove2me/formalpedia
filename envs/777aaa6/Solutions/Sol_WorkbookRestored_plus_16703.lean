-- Prove2me | solution 1 for WorkbookRestored.plus_16703
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:23.866688+00:00
-- url     : https://prove2.me/submissions/dd152c4e-54c5-42f9-96f9-7471bf4afb52

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_16703.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution {a b c : ℝ} {y z : ℝ} : (a * sin y + b * cos z + c) ^ 2 ≤ (a ^ 2 + b ^ 2 + c ^ 2) * (sin y ^ 2 + cos z ^ 2 + 1 ^ 2)   := by
  apply le_of_sub_nonneg
  ring_nf
  nlinarith [sq_nonneg (a * sin y - b * cos z), sq_nonneg (a * cos z - b * sin y), sq_nonneg (c * sin y - a), sq_nonneg (c * cos z - b)]
#print axioms solution
