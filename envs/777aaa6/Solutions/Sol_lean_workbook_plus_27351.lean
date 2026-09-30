-- Prove2me | solution 1 for lean_workbook_plus_27351
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T03:23:58.892049+00:00
-- url     : https://prove2.me/submissions/6c5e5f6f-2ccb-4fb3-8c94-1dc511516552

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 1) (h : a^2 * b^2 * (1 / a^3 + 1 / b^3 + 1 / c^3) = 4) : a * b / (b + c^2) + b * c / (c + a^2) + c * a / (a + b^2) ≥ a + b + c - 1 := by
  rw [hab]
  norm_num
  positivity
