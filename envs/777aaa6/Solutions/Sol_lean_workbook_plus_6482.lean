-- Prove2me | solution 1 for lean_workbook_plus_6482
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:26.666451+00:00
-- url     : https://prove2.me/submissions/c183cf66-ccc0-4f14-8663-ba46142da05d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) : 2.5 * x ^ 2 + 3 * x - 4 = 0 ↔ x = -2 ∨ x = 0.8 := by
  constructor
  · intro h
    have hf : (x+2)*(x-4/5)=0 := by nlinarith
    rcases mul_eq_zero.mp hf with h | h
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num
