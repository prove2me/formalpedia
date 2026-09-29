-- Prove2me | solution 1 for lean_workbook_plus_54151
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:03:43.386747+00:00
-- url     : https://prove2.me/submissions/0fa88a99-a613-4df0-a8dc-abe9a68c1bcd

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p : ℚ) (hp : p ≠ 0) (hp1 : p + 1 ≠ 0) : 1 / (p * (p + 1)) = 1 / p - 1 / (p + 1) := by
  (intros; field_simp; ring)
