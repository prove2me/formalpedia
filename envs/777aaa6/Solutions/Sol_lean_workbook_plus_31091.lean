-- Prove2me | solution 1 for lean_workbook_plus_31091
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:44:09.794793+00:00
-- url     : https://prove2.me/submissions/79c76d6c-80f8-4023-a015-f91f4f11de4c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h : x ^ 2 + y ^ 2 = 2) : x + y ≤ 2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
