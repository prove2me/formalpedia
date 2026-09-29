-- Prove2me | solution 1 for lean_workbook_plus_59282
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:43:53.642703+00:00
-- url     : https://prove2.me/submissions/09a46b24-86ce-4100-8f05-8fd905615c2c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a ^ 2 + b ^ 2 + c ^ 2 - (a * b + a * c + b * c) ≥ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
