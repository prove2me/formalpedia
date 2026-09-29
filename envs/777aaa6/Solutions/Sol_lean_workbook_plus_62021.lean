-- Prove2me | solution 1 for lean_workbook_plus_62021
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:19:30.892522+00:00
-- url     : https://prove2.me/submissions/0f577c04-c25d-48b6-90ab-5f8f160478de

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h : x + y = 4) : 8 ≤ x ^ 2 + y ^ 2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
