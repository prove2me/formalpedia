-- Prove2me | solution 1 for lean_workbook_plus_41352
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:27:45.151684+00:00
-- url     : https://prove2.me/submissions/7572e858-78b6-4c93-949f-defd7c5e8102

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : 15 / 4 = 60 / x) :
  x = 16 := by
  have h := (eq_div_iff (ne_of_gt h₀)).mp h₁
  linarith
