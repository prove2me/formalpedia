-- Prove2me | solution 1 for lean_workbook_plus_31233
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:40:07.350618+00:00
-- url     : https://prove2.me/submissions/c6702bbb-2701-4a85-ab3a-168c5858f832

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b + c - a) ^ 2 / ((b + c) ^ 2 + a ^ 2) + (c + a - b) ^ 2 / ((c + a) ^ 2 + b ^ 2) + (a + b - c) ^ 2 / ((a + b) ^ 2 + c ^ 2) ≥ 3/5 := by
  (intros; positivity)
