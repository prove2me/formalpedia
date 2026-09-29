-- Prove2me | solution 1 for lean_workbook_plus_69145
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:31:04.118302+00:00
-- url     : https://prove2.me/submissions/224462b8-f353-49e7-b032-b9a4655dda73

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a^2 = b^2 + b * c) (hbc : b^2 = c^2 + c * a) : 1 / c = 1 / a + 1 / b := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
