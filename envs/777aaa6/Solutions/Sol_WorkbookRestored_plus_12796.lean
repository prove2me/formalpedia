-- Prove2me | solution 1 for WorkbookRestored.plus_12796
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:18:45.615612+00:00
-- url     : https://prove2.me/submissions/f0c6df06-90e5-4d40-a00d-a567742c28e2

/- Adapted from InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_12796. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) : x + 2 ≥ 2^x   := by
  obtain ⟨hx1, hx2⟩ := hx
  have h1 : 0 ≤ x + 2 := by linarith
  nlinarith [rpow_le_rpow_of_exponent_le one_le_two hx2]
#print axioms solution
