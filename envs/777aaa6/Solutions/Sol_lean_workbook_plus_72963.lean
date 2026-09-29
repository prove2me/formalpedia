-- Prove2me | solution 1 for lean_workbook_plus_72963
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:50:39.117558+00:00
-- url     : https://prove2.me/submissions/222ae8ab-089c-4a7c-a2ec-d150844ac6a6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 2 * (a + b + c) ^ 4 + 3 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 6 * (a + b + c) * (a + b) * (b + c) * (c + a) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
