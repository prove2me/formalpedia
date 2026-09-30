-- Prove2me | solution 2 for lean_workbook_plus_2230
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:32:33.299817+00:00
-- url     : https://prove2.me/submissions/ddaa8b7d-3968-449d-81f6-6c4686fcb410

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a + b) ^ 4 + (b + c) ^ 4 + (c + a) ^ 4 ≥ 8 * (a ^ 3 * (b + c) + b ^ 3 * (c + a) + c ^ 3 * (a + b)) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
