-- Prove2me | solution 1 for lean_workbook_plus_52048
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:05:16.333279+00:00
-- url     : https://prove2.me/submissions/f43b0bf6-f2c2-4697-a6ae-d5c908e42ef5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x + y = 2) : 2 * Real.sqrt (x * y) ≤ 2 := by
  (intros; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ x * y by positivity), Real.sqrt_nonneg (x * y), sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_nonneg hx hy])
