-- Prove2me | solution 1 for lean_workbook_plus_31796
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:26:33.027093+00:00
-- url     : https://prove2.me/submissions/b0154f69-aecb-4c71-a8bb-c3c383544761

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a b : ℝ)
  (h₀ : b ≠ 0)
  (h₁ : a * b * (a / b) > 0) :
  a^2 > 0 := by
  have heq : a * b * (a / b) = a^2 := by field_simp
  rw [heq] at h₁
  exact h₁
