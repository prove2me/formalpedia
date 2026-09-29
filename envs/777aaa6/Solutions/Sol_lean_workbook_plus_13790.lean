-- Prove2me | solution 1 for lean_workbook_plus_13790
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:23:22.019434+00:00
-- url     : https://prove2.me/submissions/3045037e-5ea7-4315-b07d-c64cfe7be81a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) : a ^ 3 * (b + c + d) + b ^ 3 * (a + c + d) + c ^ 3 * (a + b + d) + d ^ 3 * (a + b + c) ≤ (3 / 4 : ℝ) * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
