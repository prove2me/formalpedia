-- Prove2me | solution 1 for lean_workbook_plus_81884
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:36:18.294544+00:00
-- url     : https://prove2.me/submissions/a5b4513b-1a18-47a9-9be2-a29829d1f8a1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) :
  2 * a^2 + 2 * b^2 ≥ (a + b)^2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
