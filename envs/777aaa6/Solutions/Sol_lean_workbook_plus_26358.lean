-- Prove2me | solution 1 for lean_workbook_plus_26358
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:33:02.349459+00:00
-- url     : https://prove2.me/submissions/a9f6c8d4-f72d-40aa-abcd-0b806b1105ce

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ x : ℝ, x ≠ 0 ∧ x ≠ -1 → 1 / (x ^ 2 + x) = 1 / x - 1 / (x + 1) := by
  intro x hx
  have h1 : x+1 ≠ 0 := by intro h; apply hx.2; linarith
  have h2 : x^2+x ≠ 0 := by rw [show x^2+x=x*(x+1) by ring]; exact mul_ne_zero hx.1 h1
  field_simp [hx.1,h1,h2] <;> ring
