-- Prove2me | solution 1 for lean_workbook_plus_68249
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:12:52.578361+00:00
-- url     : https://prove2.me/submissions/1a3a05b7-a1f2-4152-86e8-39143ea6d781

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a * (b * b + c * c - a * a) + b * (c * c + a * a - b * b) + c * (a * a + b * b - c * c) ≤ 3 * a * b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
