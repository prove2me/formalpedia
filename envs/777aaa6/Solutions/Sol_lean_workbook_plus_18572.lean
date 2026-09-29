-- Prove2me | solution 1 for lean_workbook_plus_18572
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:57:03.0277+00:00
-- url     : https://prove2.me/submissions/bb5e59b8-e9db-4692-9557-49d4b0765f70

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : x ^ 2 + y ^ 2 - 2 * x * y ≥ 0 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
