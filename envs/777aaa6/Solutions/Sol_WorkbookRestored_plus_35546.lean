-- Prove2me | solution 1 for WorkbookRestored.plus_35546
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:51.021071+00:00
-- url     : https://prove2.me/submissions/5c3da076-3a1f-45e0-9021-72c8c99c032a

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_35546.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (hx : x ≠ 0) (h : x ≠ π / 2) : (sin x / cos x) * (sin x / sin x) + (cos x / sin x) * (cos x / cos x) = 1 / (sin x * cos x)   := by
  ring_nf
  field_simp [hx,h]
  rw [sin_sq_add_cos_sq]
#print axioms solution
