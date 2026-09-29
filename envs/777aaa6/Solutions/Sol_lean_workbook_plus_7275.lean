-- Prove2me | solution 1 for lean_workbook_plus_7275
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:05:59.151766+00:00
-- url     : https://prove2.me/submissions/9c7dda92-a42c-4994-b095-992a2fa50b6a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
