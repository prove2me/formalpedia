-- Prove2me | solution 1 for lean_workbook_plus_33863
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:52:46.911189+00:00
-- url     : https://prove2.me/submissions/84d9c63e-a402-4e65-9606-90e573dc641c

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution {n : ℤ} (hn : n^2 + 5*n + 7 = 1) : n = -2 ∨ n = -3 := by
  have h : (n+2)*(n+3) = 0 := by nlinarith
  rcases mul_eq_zero.mp h with h | h
  · left; omega
  · right; omega
