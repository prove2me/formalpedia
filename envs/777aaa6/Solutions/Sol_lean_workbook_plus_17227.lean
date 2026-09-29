-- Prove2me | solution 1 for lean_workbook_plus_17227
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:30:41.656378+00:00
-- url     : https://prove2.me/submissions/d6be186c-7b41-48c0-90f7-acd3a28ab0d7

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (k : ℝ) : k^2 + 10 * k + 16 = 0 ↔ k = -2 ∨ k = -8 := by
  constructor
  · intro h
    have hf : (k + 2) * (k + 8) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with hf | hf
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num
