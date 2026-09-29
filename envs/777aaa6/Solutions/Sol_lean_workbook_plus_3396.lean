-- Prove2me | solution 1 for lean_workbook_plus_3396
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:08:31.308601+00:00
-- url     : https://prove2.me/submissions/973873a9-43c0-4080-b891-49659b898297

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b: ℝ) : 2 * (a ^ 2 + b ^ 2) ≥ (a - b) ^ 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
