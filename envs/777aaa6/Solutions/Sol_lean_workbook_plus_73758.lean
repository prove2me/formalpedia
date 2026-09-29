-- Prove2me | solution 1 for lean_workbook_plus_73758
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:21:02.869398+00:00
-- url     : https://prove2.me/submissions/c44d39b9-3b4d-4939-828c-24b29ada692e

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ)
  (h₀ : 1 + 2 / b - 3 / c = a)
  (h₁ : -1 / a + 2 + 3 / c = b)
  (h₂ : 1 / a - 2 / b + 3 = c) :
  a + b + c = 6 := by
  simp only [neg_div] at h₁
  linarith
