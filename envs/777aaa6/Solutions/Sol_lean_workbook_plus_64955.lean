-- Prove2me | solution 1 for lean_workbook_plus_64955
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:50:23.526116+00:00
-- url     : https://prove2.me/submissions/aa63405d-7702-4b83-876d-f315fcadccf0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c: ℝ) : 16 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 3 * ((a + b) ^ 4 + (b + c) ^ 4 + (c + a) ^ 4) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
