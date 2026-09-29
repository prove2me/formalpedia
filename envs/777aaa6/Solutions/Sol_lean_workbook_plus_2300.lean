-- Prove2me | solution 1 for lean_workbook_plus_2300
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:24:37.991098+00:00
-- url     : https://prove2.me/submissions/fa249db3-0070-48e6-bf58-c3cfdbc26942

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : x = 20 / 100 * 23) (hy : y = 23 / 100 * 20) : x * y = 21.16 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
