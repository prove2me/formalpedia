-- Prove2me | solution 1 for lean_workbook_plus_48452
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:28:51.745318+00:00
-- url     : https://prove2.me/submissions/e0f53904-499c-41cf-af40-83f6ac2fba59

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (b c d : ℂ)
  (h₀ : b ≠ 0)
  (h₁ : 3 * b * c - 2 * b^3 = d) :
  c = (d + 2 * b^3) / (3 * b) := by
  apply (eq_div_iff (mul_ne_zero (by norm_num) h₀)).2
  linear_combination h₁
