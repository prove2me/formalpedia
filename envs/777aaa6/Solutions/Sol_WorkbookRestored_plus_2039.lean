-- Prove2me | solution 1 for WorkbookRestored.plus_2039
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:17:46.018187+00:00
-- url     : https://prove2.me/submissions/32adff8a-d1d5-46ca-9733-ec03031c4853

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_2039.
   Draft repair: only required imports and namespaces are restored. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : sin 30 * cos 10 - sin 10 * cos 30 = sin 20   := by
  rw [mul_comm (sin 10) (cos 30), ← Real.sin_sub]
  norm_num <;> rfl
#print axioms solution
