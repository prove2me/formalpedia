-- Prove2me | solution 1 for lean_workbook_plus_13414
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:22:50.488069+00:00
-- url     : https://prove2.me/submissions/fb47c9df-f460-4f13-85cc-cae3d1a89ea0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h : x*y ≥ 1) : (x^2 + 1)^(-1:ℤ) + (y^2 + 1)^(-1:ℤ) ≥ 2/(1 + x*y) := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
