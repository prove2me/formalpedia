-- Prove2me | solution 1 for lean_workbook_plus_43848
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:28:08.080946+00:00
-- url     : https://prove2.me/submissions/8fea7b31-59e2-4c4b-aaee-328089943a07

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 6 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 + 3 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) * (a + b + c) ≥ (a + b + c) ^ 4 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
