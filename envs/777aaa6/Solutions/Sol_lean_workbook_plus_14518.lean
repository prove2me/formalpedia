-- Prove2me | solution 1 for lean_workbook_plus_14518
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:30:46.401274+00:00
-- url     : https://prove2.me/submissions/918c9dea-15d8-424f-a9d8-4a4052c2cd5b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (h1 : a + b + c + d = 4) (h2 : a * b + c * d = 8) : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≥ 16 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
