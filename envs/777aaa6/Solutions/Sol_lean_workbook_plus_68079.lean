-- Prove2me | solution 1 for lean_workbook_plus_68079
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:13:12.874036+00:00
-- url     : https://prove2.me/submissions/0575530c-ab14-4b07-ac76-140dff5a72ef

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h : x + y > 0) : 8 * (x ^ 2 - x * y + y ^ 2) ^ 2 - (x ^ 2 + y ^ 2) * (x ^ 2 + 2 * x * y + y ^ 2) ≥ 0 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
