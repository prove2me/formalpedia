-- Prove2me | solution 1 for WorkbookRestored.plus_60454
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:06.112991+00:00
-- url     : https://prove2.me/submissions/bffad04d-2710-4d32-b75b-406e8dd04c8b

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_60454.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (t : ℝ) (x : ℝ) (h₁ : t = Real.tan (x / 2)) : (10 * t / (1 + t^2) - 3 * (1 - t^2) / (1 + t^2) - 3 = 0) ↔ t = 3 / 5   := by
  constructor <;> intro h <;> field_simp [h₁, h] at h₁ h ⊢ <;> linarith
#print axioms solution
