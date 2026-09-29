-- Prove2me | solution 1 for WorkbookRestored.plus_50860
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:08:46.853191+00:00
-- url     : https://prove2.me/submissions/28f3508a-8885-468d-8609-f17126eb9e19

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_50860.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (k : ℤ) : (Real.cos x = Real.pi / 2 + Real.sin x + 2 * Real.pi * k) ↔ (Real.cos (x + Real.pi / 4) = (2 * Real.sqrt 2)⁻¹ * (4 * k + 1) * Real.pi)   := by
  rw [cos_add,cos_pi_div_four,sin_pi_div_four]
  field_simp
  norm_num
  constructor <;> intro h <;> linarith
#print axioms solution
