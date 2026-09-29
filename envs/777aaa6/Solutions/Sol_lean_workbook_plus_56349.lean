-- Prove2me | solution 1 for lean_workbook_plus_56349
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:55:28.759778+00:00
-- url     : https://prove2.me/submissions/28db65e2-51c6-43cb-8be2-fc8c44cb300d

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a : ℝ) (h : a >= 1) : a^4 + 1/a^4 ≥ a + 1/a := by
  have ha : 0 < a := by linarith
  have hi : a^4+1/a^4-(a+1/a) = (a-1)^2*(a^6+2*a^5+3*a^4+3*a^3+3*a^2+2*a+1)/a^4 := by
    field_simp
    ring
  have hn : 0 ≤ (a-1)^2*(a^6+2*a^5+3*a^4+3*a^3+3*a^2+2*a+1)/a^4 := by positivity
  linarith
