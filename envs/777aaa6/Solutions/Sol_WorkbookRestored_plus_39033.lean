-- Prove2me | solution 1 for WorkbookRestored.plus_39033
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:58.392451+00:00
-- url     : https://prove2.me/submissions/10fa6bba-a166-4eda-947a-184b79a58c7f

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_39033.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution  (x : ℝ) (k : ℤ) :
  (Real.cos x = Real.pi / 2 - Real.sin x + 2 * Real.pi * k) ↔
  (Real.sin (x + Real.pi / 4) = (4 * k + 1) * Real.pi / (2 * Real.sqrt 2))   := by
  rw [sin_add, cos_pi_div_four, sin_pi_div_four]
  have hs := sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hn : sqrt (2:ℝ) ≠ 0 := ne_of_gt (sqrt_pos.2 (by norm_num))
  field_simp
  norm_num at *
  constructor <;> intro h <;> nlinarith
#print axioms solution
