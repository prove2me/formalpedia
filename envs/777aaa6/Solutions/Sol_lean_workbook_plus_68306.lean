-- Prove2me | solution 1 for lean_workbook_plus_68306
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:12:47.262939+00:00
-- url     : https://prove2.me/submissions/ff3a1b3d-e2eb-421b-a684-667b4ec2ceab

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a ^ 3 + b ^ 3 + c ^ 3 - 2 * (a ^ 2 * (b + c) + b ^ 2 * (a + c) + c ^ 2 * (a + b)) ≤ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
