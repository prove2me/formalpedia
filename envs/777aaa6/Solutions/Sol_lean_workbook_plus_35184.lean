-- Prove2me | solution 1 for lean_workbook_plus_35184
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:42:21.975073+00:00
-- url     : https://prove2.me/submissions/ee7f1bc0-6bd4-4b37-a150-c83c6d6737b1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (habc : a * b * c = 1) : (a^2 + 1) / b / c + (b^2 + 1) / c / a + (c^2 + 1) / a / b = (a^3 + b^3 + c^3 + a + b + c) / a / b / c := by
  (intros; field_simp; ring)
