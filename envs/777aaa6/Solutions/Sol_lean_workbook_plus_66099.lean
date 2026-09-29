-- Prove2me | solution 1 for lean_workbook_plus_66099
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:31:42.605295+00:00
-- url     : https://prove2.me/submissions/61a674eb-16ed-4efa-8c0d-c34dc5f71c59

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : 2 * a * b / (a + b) = 1 / ((1 / a + 1 / b) / 2) := by
  (intros; field_simp; ring)
