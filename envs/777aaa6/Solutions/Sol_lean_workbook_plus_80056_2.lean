-- Prove2me | solution 2 for lean_workbook_plus_80056
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:00:23.28206+00:00
-- url     : https://prove2.me/submissions/e483a12a-9302-44b4-a0ec-ec266f6d7660

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 - a / (1 + a + a * b) - b / (1 + b + b * c) - c / (1 + c + c * a) : ℝ) = (a * b * c - 1) ^ 2 / ((1 + a + a * b) * (1 + b + b * c) * (1 + c + c * a)) := by
  (intros; field_simp; ring)
