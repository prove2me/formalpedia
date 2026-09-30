-- Prove2me | solution 1 for lean_workbook_plus_78010
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:09:59.112743+00:00
-- url     : https://prove2.me/submissions/7aa124dc-200c-4538-a6c5-fcb814f70d9b

import Mathlib

set_option autoImplicit false

theorem solution (x : ℝ) (hx : x > 0) : x + 1 / x ≥ 2 := by
  calc
    2 ≤ (x ^ 2 + 1) / x := (le_div_iff₀ hx).2 (by nlinarith [sq_nonneg (x - 1)])
    _ = x + 1 / x := by field_simp
