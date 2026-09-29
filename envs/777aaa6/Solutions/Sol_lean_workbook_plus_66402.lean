-- Prove2me | solution 1 for lean_workbook_plus_66402
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:32:18.530852+00:00
-- url     : https://prove2.me/submissions/2268c7fd-a7b1-460c-80d4-e5c5685c306a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h : x + y = 1) : x * y ≤ 1 / 4 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
