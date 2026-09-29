-- Prove2me | solution 1 for lean_workbook_plus_38873
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:54:25.024466+00:00
-- url     : https://prove2.me/submissions/4196a934-1853-4e31-8daa-2ef56dc402bd

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1) : 2 ≥ a + b + c + d := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
