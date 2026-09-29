-- Prove2me | solution 1 for lean_workbook_plus_15175
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:59:50.550453+00:00
-- url     : https://prove2.me/submissions/2f497287-a690-4c79-b8f3-d73400bc04f2

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (b : ℝ) (h : (b - 1) ^ 2 * (2 * b + 7) = 0) : b = 1 ∨ b = -7 / 2 := by
  rcases mul_eq_zero.mp h with h | h
  · left; nlinarith
  · right; linarith
