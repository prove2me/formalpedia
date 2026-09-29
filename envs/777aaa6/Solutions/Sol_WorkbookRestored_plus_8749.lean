-- Prove2me | solution 1 for WorkbookRestored.plus_8749
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:34:56.145978+00:00
-- url     : https://prove2.me/submissions/ba1e90e6-8d67-443a-b1f3-dfea92eecbc4

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_8749.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x : ℝ, 0 < x ∧ x ≤ π / 2 → 0 < sin x ∧ sin x ≤ 1   := by
  exact fun x hx => ⟨sin_pos_of_pos_of_lt_pi hx.1 (by linarith), sin_le_one x⟩
#print axioms solution
