-- Prove2me | solution 1 for WorkbookRestored.plus_46600
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:05:12.361787+00:00
-- url     : https://prove2.me/submissions/19699666-0455-45ee-b877-031065d2ff37

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_46600.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x y n : ℝ) : (cos (x - y) - cos (x + y) = n ↔ 2 * cos ((x - y) / 2) ^ 2 - 2 * cos ((x + y) / 2) ^ 2 = n)   := by
  have h1 := cos_two_mul ((x-y)/2)
  have h2 := cos_two_mul ((x+y)/2)
  rw [show 2*((x-y)/2)=x-y by ring] at h1
  rw [show 2*((x+y)/2)=x+y by ring] at h2
  constructor <;> intro h <;> linarith
#print axioms solution
