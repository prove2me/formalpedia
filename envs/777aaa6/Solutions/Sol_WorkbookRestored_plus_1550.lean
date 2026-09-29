-- Prove2me | solution 1 for WorkbookRestored.plus_1550
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:17:42.62652+00:00
-- url     : https://prove2.me/submissions/7679b328-6ede-4808-a3a1-5b563a8426d7

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_1550.
   Draft repair: only required imports and namespaces are restored. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) :  x ^ 2 * Real.sin x + x * Real.cos x + x ^ 2 + 1 / 2 > 0   := by
  have h : 0 ≤ (x * sin x + cos x) ^ 2 := sq_nonneg _
  have h1 := sq_nonneg (x * cos x - sin x)
  field_simp [sin_sq, cos_sq] at h h1 ⊢
  have h2 := sq_nonneg (x ^ 2 - 1)
  nlinarith [sin_sq_add_cos_sq x]
#print axioms solution
