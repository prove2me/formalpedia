-- Prove2me | solution 1 for lean_workbook_plus_74706
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:52:39.850285+00:00
-- url     : https://prove2.me/submissions/2a35b90e-f030-42ac-af79-7095999eae0c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : 2 * x * y ≤ x ^ 2 + y ^ 2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
