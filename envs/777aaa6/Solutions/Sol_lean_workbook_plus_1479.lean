-- Prove2me | solution 1 for lean_workbook_plus_1479
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:51:56.348832+00:00
-- url     : https://prove2.me/submissions/22dd1ea5-dcc7-4dc8-bccd-93218e9a415e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : a * b * c ≠ 0) : (a / b : ℚ) ^ 3 - (a / b + b / c + c / a) * (a / b) ^ 2 + (a / c + c / b + b / a) * (a / b) - 1 = 0 := by
  (intros; field_simp; ring)
