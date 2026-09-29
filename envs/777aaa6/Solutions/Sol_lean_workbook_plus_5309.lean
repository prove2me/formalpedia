-- Prove2me | solution 1 for lean_workbook_plus_5309
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:17:06.677885+00:00
-- url     : https://prove2.me/submissions/c47d9c57-2247-4e95-8a72-0f951a5a3e30

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h : x + y = 10) : x*y ≤ 25 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
