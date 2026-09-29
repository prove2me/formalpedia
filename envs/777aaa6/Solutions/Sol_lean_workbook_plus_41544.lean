-- Prove2me | solution 1 for lean_workbook_plus_41544
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:30:13.050023+00:00
-- url     : https://prove2.me/submissions/443cf43e-4b76-4d57-9a01-1b218c6c44c8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : (a + b) * (a + c) * (b + c) / 8 ≥ (2 * a + b) * (2 * b + c) * (2 * c + a) / 27 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
