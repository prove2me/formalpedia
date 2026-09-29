-- Prove2me | solution 1 for lean_workbook_plus_65567
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:29:04.367655+00:00
-- url     : https://prove2.me/submissions/1632fe0d-5ef8-490e-b799-6e8c7205b85e

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : (4:ℝ) / 10 * (16:ℝ) / (16 + n) + 6 / 10 * n / (16 + n) = 29 / 50) :
  n = 144 := by
  have hd : (16 : ℝ) + (n : ℝ) ≠ 0 := by positivity
  field_simp [hd] at h₁
  have hn : (n : ℝ) = 144 := by linarith
  exact_mod_cast hn
