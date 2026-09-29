-- Prove2me | solution 1 for lean_workbook_plus_29273
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:04:35.657704+00:00
-- url     : https://prove2.me/submissions/cbf99a6a-06a8-497b-bfc6-1da7eb08aa9f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h : x ^ 2 < x * y ∧ x * y < 1 / 100) : x < 1 / 10 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
