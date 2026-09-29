-- Prove2me | solution 1 for lean_workbook_plus_74140
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:51:36.330879+00:00
-- url     : https://prove2.me/submissions/a1bda8e7-c8b4-45d0-99ef-a9b464c9fa4e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : x > 0) (hy : y > 0) : 1 / (x + y) ≤ (1 / 4) * (1 / x + 1 / y) := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
