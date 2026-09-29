-- Prove2me | solution 1 for WorkbookRestored.plus_73087
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:24.316978+00:00
-- url     : https://prove2.me/submissions/f9e1a1f1-91f2-4b2a-919c-d120f1f0ec67

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_73087.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution :
  ∀ A B : ℝ, (sin A * cos B = sin B * cos A) ↔ sin (A - B) = 0   := by
  refine' fun A B => ⟨fun h => _, fun h => _⟩ <;> linarith [sin_sub A B, h]
#print axioms solution
