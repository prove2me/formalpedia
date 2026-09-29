-- Prove2me | solution 1 for lean_workbook_plus_8086
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:58:40.00783+00:00
-- url     : https://prove2.me/submissions/b2c67cf0-1ed9-4b5e-ac2f-3cb9dea71777

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : (a + b - 1) ^ 2 / c + (b + c - 1) ^ 2 / a + (c + a - 1) ^ 2 / b = a + b + c) : a * b * c ≤ 1 := by
  (intros; simp_all)
