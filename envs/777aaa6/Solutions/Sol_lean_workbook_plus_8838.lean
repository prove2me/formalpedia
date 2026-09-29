-- Prove2me | solution 1 for lean_workbook_plus_8838
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:57:40.892192+00:00
-- url     : https://prove2.me/submissions/4acb5190-2b4b-4f4a-8a11-91cd24dd2c47

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a + c) ^ 2 * (b + c) ^ 2 ≥ 4 * c * (a + b) * (c ^ 2 + a * b) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
