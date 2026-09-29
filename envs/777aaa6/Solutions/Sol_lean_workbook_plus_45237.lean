-- Prove2me | solution 1 for lean_workbook_plus_45237
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:49:44.615712+00:00
-- url     : https://prove2.me/submissions/0fa25048-0933-4f73-bc17-f28f0e783328

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a + b + c = 3) : a * b + b * c + c * a ≤ 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
