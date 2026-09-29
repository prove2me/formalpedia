-- Prove2me | solution 1 for lean_workbook_plus_56997
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:28:37.358218+00:00
-- url     : https://prove2.me/submissions/8438f113-8c63-4ea6-bb2c-1e1c10d42211

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : (3 / 2) / 400 = (3 / 16) / x) :
  x = 50 := by
  field_simp [ne_of_gt h₀] at h₁
  linarith
