-- Prove2me | solution 1 for lean_workbook_plus_14453
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:52:10.216737+00:00
-- url     : https://prove2.me/submissions/7ac52002-248c-443b-948a-8a6d2f18a5de

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y m n : ℝ) (hx : 0 < x) (hy : 0 < y) (hm : 0 < m) (hn : 0 < n) (hxy : x + y = m + n) (hmn : x*y = m*n) : x = m ∨ x = n := by
  have h : (x-m)*(x-n) = 0 := by nlinarith
  rcases mul_eq_zero.mp h with h | h
  · left; linarith
  · right; linarith
