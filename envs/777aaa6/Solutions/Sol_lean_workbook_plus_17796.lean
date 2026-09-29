-- Prove2me | solution 1 for lean_workbook_plus_17796
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:11:22.135682+00:00
-- url     : https://prove2.me/submissions/b6649392-65ad-4927-a2cc-499c082b8c2b

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000


theorem solution (a : ℝ) (h : (a + 1) * (a ^ 3 - 4) = 0) : a = -1 ∨ a ^ 3 = 4 := by
  rcases mul_eq_zero.mp h with h | h
  · left; linarith
  · right; linarith
