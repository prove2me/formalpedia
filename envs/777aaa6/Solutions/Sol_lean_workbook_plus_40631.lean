-- Prove2me | solution 1 for lean_workbook_plus_40631
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:07:13.005386+00:00
-- url     : https://prove2.me/submissions/3a2d2be4-be02-401e-b815-b8fa7bf1407a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (x : ℝ) : 5 * x ^ 4 - 5 * x ^ 2 + 120 * x = 0 ↔ x = 0 ∨ x = -3 := by
  have hq : 0 < x ^ 2 - 3 * x + 8 := by nlinarith [sq_nonneg (2 * x - 3)]
  have heq : 5 * x ^ 4 - 5 * x ^ 2 + 120 * x = 5 * (x * (x + 3)) * (x ^ 2 - 3 * x + 8) := by ring
  rw [heq]
  constructor
  · intro h
    have hfac := (mul_eq_zero.mp h).resolve_right (ne_of_gt hq)
    have hxprod := (mul_eq_zero.mp hfac).resolve_left (by norm_num : (5 : ℝ) ≠ 0)
    rcases mul_eq_zero.mp hxprod with hzero | hthree
    · exact Or.inl hzero
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> norm_num
