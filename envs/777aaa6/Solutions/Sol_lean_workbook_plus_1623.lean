-- Prove2me | solution 1 for lean_workbook_plus_1623
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:20:18.966023+00:00
-- url     : https://prove2.me/submissions/476077d3-e274-4947-aa60-df8b3473e959

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) : x^2 - 9*x + 20 = 0 ↔ x = 4 ∨ x = 5 := by
  have he : x^2-9*x+20 = (x-4)*(x-5) := by ring
  rw [he,mul_eq_zero]
  constructor
  · rintro (h|h)
    · left; linarith
    · right; linarith
  · rintro (rfl|rfl) <;> norm_num
