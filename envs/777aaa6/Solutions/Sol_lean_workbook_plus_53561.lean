-- Prove2me | solution 1 for lean_workbook_plus_53561
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:46:11.146875+00:00
-- url     : https://prove2.me/submissions/d1ac8f38-6cd6-493f-9433-384a49a1d5a1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : x > 0) (hy : y > 0) : (y / x + x / y + (x * y) / (x + y) ^ 2) ≥ 9 / 4 := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
