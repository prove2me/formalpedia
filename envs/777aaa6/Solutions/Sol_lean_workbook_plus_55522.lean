-- Prove2me | solution 1 for lean_workbook_plus_55522
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:13:48.269691+00:00
-- url     : https://prove2.me/submissions/62f39909-6e98-4b9f-8f6d-93c64c7c428d

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) (hx : 1 ≤ x) : x ^ 12 - x ^ 9 + x ^ 4 - x + 1 > 0   := by
  have h12 : x ^ 9 ≤ x ^ 12 := pow_le_pow_right₀ hx (by norm_num)
  have h4 : x ^ 1 ≤ x ^ 4 := pow_le_pow_right₀ hx (by norm_num)
  norm_num at h4
  linarith

#print axioms solution
