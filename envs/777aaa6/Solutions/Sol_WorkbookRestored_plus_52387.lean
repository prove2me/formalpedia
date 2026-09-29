-- Prove2me | solution 1 for WorkbookRestored.plus_52387
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:24:48.171419+00:00
-- url     : https://prove2.me/submissions/7bd86cea-aca7-4800-bbea-d8b8b36198aa

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_52387.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (θ : ℝ) (h : cos θ ≠ 0) : √((1 + 1 / cos θ) / (1 / cos θ - 1)) = √((cos θ + 1) / (1 - cos θ))   := by
  field_simp [h]
#print axioms solution
