-- Prove2me | solution 1 for lean_workbook_plus_40208
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:26:10.788417+00:00
-- url     : https://prove2.me/submissions/be34e216-c67f-4e6b-9279-6ff8f1b9296e

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (x : ℝ) : x^3 + x^2 - x - 1 = 0 ↔ x = -1 ∨ x = 1 := by
  constructor
  · intro h
    have hf : (x - 1) * (x + 1)^2 = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with hf | hf
    · right; linarith
    · left; nlinarith
  · rintro (rfl | rfl) <;> norm_num
