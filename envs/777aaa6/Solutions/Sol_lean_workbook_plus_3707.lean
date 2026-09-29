-- Prove2me | solution 1 for lean_workbook_plus_3707
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:51:45.369872+00:00
-- url     : https://prove2.me/submissions/fc82abb3-fc45-44d3-b552-81e74c48e554

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y : ℝ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x + y = 7)
  (h₂ : (x^2 + y^2) / (x * y) = 25 / 12) :
  x * y = 12 := by
  have hxy : x*y ≠ 0 := mul_ne_zero (ne_of_gt h₀.1) (ne_of_gt h₀.2)
  have he := (div_eq_iff hxy).mp h₂
  nlinarith [sq_nonneg (x+y-7)]
