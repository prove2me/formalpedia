-- Prove2me | solution 1 for WorkbookRestored.plus_24031
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:18:54.349827+00:00
-- url     : https://prove2.me/submissions/3dc2a7cc-f4d3-411f-87bf-594222f7eb1f

/- Adapted from InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_24031. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (a : ℝ) (h : x = 0 ∨ x = 1) : (1 + a) ^ x = 1 + a * x   := by
  rcases h with (rfl | rfl) <;> simp [add_mul, mul_add, mul_comm, mul_left_comm]
#print axioms solution
