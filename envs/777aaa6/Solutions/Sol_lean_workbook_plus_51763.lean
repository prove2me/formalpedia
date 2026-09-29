-- Prove2me | solution 1 for lean_workbook_plus_51763
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:05:42.058185+00:00
-- url     : https://prove2.me/submissions/56c00108-5c06-4b4c-a937-531b2acf375f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : 2 / (1 / a + 1 / b) = 2 * a * b / (a + b) := by
  (intros; field_simp; ring)
