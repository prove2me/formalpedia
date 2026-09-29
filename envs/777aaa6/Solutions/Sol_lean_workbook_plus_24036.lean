-- Prove2me | solution 1 for lean_workbook_plus_24036
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:15:51.558136+00:00
-- url     : https://prove2.me/submissions/f13b340f-1ee4-4f52-a3a2-2f6d1aec9bbd

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 4 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 9 * (a + b + c) * (b + c - a) * (c + a - b) * (a + b - c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
