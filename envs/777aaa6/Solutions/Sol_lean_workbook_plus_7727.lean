-- Prove2me | solution 1 for lean_workbook_plus_7727
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:59:35.197681+00:00
-- url     : https://prove2.me/submissions/562ac8a1-84aa-4453-9cc1-33baf90c4383

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : (a + b) * (1 / a + 1 / b) - 4 = (a - b) ^ 2 / (a * b) := by
  (intros; field_simp; ring)
