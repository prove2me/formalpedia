-- Prove2me | solution 1 for lean_workbook_plus_74350
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:52:07.504802+00:00
-- url     : https://prove2.me/submissions/32471d41-7fc1-47d6-b8bf-4021f382da6b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : (x ^ 2 + y ^ 2 + z ^ 2) / 3 ≥ (x + y + z) ^ 2 / 3 ^ 2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
