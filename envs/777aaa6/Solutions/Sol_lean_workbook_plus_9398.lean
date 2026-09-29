-- Prove2me | solution 1 for lean_workbook_plus_9398
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:39:01.198544+00:00
-- url     : https://prove2.me/submissions/7e6df1ac-022a-4fe5-a6a6-e702d84634d5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h : x + y + z >= x * y * z) : x ^ 2 + y ^ 2 + z ^ 2 >= x * y * z := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
