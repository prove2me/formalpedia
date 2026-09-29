-- Prove2me | solution 1 for lean_workbook_plus_69024
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:31:16.374787+00:00
-- url     : https://prove2.me/submissions/3af7add0-a4de-40c6-b433-91b401ebb5e7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : x > 0 ∧ y > 0 ∧ z > 0) (h : x^3 + y^3 + z^3 = 81) : x + y + z ≤ 9 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
