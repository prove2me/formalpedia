-- Prove2me | solution 1 for lean_workbook_plus_80386
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:00:49.874905+00:00
-- url     : https://prove2.me/submissions/cce8e881-25f0-4781-8366-3d68d8782dd2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + c * a) + (a * b + b * c + c * a) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
