-- Prove2me | solution 1 for lean_workbook_plus_4148
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:08:03.310378+00:00
-- url     : https://prove2.me/submissions/ee93e849-69c7-4c7b-b9ee-597fc9181e76

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : x ^ 4 + y ^ 4 + z ^ 4 ≥ x ^ 2 * y * z + y ^ 2 * z * x + z ^ 2 * x * y := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
