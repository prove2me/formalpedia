-- Prove2me | solution 1 for WorkbookRestored.plus_16072
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:20.82063+00:00
-- url     : https://prove2.me/submissions/cb9eee89-8ab6-4eab-8bd4-5e7c04380767

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_16072.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ k x, Real.cos (2 * k * x) * Real.cos x = (1 / 2) * (Real.cos ((2 * k - 1) * x) + Real.cos ((2 * k + 1) * x))   := by
  intro k x
  rw [show (2*k-1)*x = 2*k*x-x by ring,
      show (2*k+1)*x = 2*k*x+x by ring,
      cos_sub, cos_add]
  ring
#print axioms solution
