-- Prove2me | solution 1 for WorkbookRestored.plus_32948
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:40.539789+00:00
-- url     : https://prove2.me/submissions/945ff19d-0804-4c8b-83dd-bd58e6490927

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_32948.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (n : ℕ) (D : ℝ) : |D - n * Real.log 2| < Real.sqrt n + 1 ↔ n * Real.log 2 - Real.sqrt n - 1 < D ∧ D < n * Real.log 2 + Real.sqrt n + 1   := by
  rw [abs_lt, sub_lt_iff_lt_add, sub_lt_iff_lt_add]
  refine' ⟨fun h => ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩, fun h => ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩⟩
#print axioms solution
