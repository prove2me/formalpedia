-- Prove2me | solution 1 for WorkbookRestored.plus_77615
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:29.272986+00:00
-- url     : https://prove2.me/submissions/4abccf5c-8170-4a2f-bd45-922594ea80dd

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_77615.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (u v w : ℂ) (h : u + v + w = 0) :
  Complex.cos u ^ 2 + Complex.cos v ^ 2 + Complex.cos w ^ 2 =
    1 + 2 * Complex.cos u * Complex.cos v * Complex.cos w   := by
  have h1 : w = -(u + v) := by linear_combination h
  simp [h1, Complex.cos_add, Complex.cos_neg, Complex.sin_neg, sub_eq_add_neg]
  ring_nf
  simp [Complex.sin_sq, Complex.cos_sq, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  ring_nf
#print axioms solution
