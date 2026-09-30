-- Prove2me | solution 1 for lean_workbook_plus_79341
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:10:01.686978+00:00
-- url     : https://prove2.me/submissions/dacfc0bf-0f7a-4e07-a8e3-af271d62fb7b

import Mathlib

set_option autoImplicit false

theorem solution (z : ℂ) : 5 * z * (z + 8) = 0 ↔ z = 0 ∨ z = -8 := by
  simp [mul_eq_zero, add_eq_zero_iff_eq_neg]
