-- Prove2me | solution 1 for lean_workbook_plus_70012
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:53:00.914778+00:00
-- url     : https://prove2.me/submissions/5c88759a-c1d9-4c74-8bc7-4335a958b42d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (A B C: ℝ) : (A + B + C) ^ 2 ≥ 3 * (A * B + B * C + C * A) := by
  (intros; nlinarith [sq_nonneg (A), sq_nonneg (B), sq_nonneg (C), sq_nonneg (A - B), sq_nonneg (A - C), sq_nonneg (B - C), sq_nonneg (A + B), sq_nonneg (A + C), sq_nonneg (B + C)])
