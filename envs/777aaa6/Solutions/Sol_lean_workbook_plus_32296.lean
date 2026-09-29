-- Prove2me | solution 1 for lean_workbook_plus_32296
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:39:42.677964+00:00
-- url     : https://prove2.me/submissions/fd8bed20-2667-4896-8566-6fbf021ab520

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℤ) : (a + b - c) ^ 2 + (b + c - a) ^ 2 + (c + a - b) ^ 2 ≥ a ^ 2 + b ^ 2 + c ^ 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
