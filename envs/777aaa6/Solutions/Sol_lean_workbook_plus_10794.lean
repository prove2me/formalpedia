-- Prove2me | solution 1 for lean_workbook_plus_10794
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:26:59.394484+00:00
-- url     : https://prove2.me/submissions/32037fd8-5357-49b7-b43f-7c44005934b2

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a b : ℝ)
  (h₀ : a + b = 4)
  (h₁ : a * b = 7 / 2) :
  1 / (2 * a) + 1 / (2 * b) = 4 / 7 := by
  have ha : a ≠ 0 := by intro h; rw [h] at h₁; norm_num at h₁
  have hb : b ≠ 0 := by intro h; rw [h] at h₁; norm_num at h₁
  apply (eq_div_iff (by norm_num : (7 : ℝ) ≠ 0)).2
  field_simp
  nlinarith
