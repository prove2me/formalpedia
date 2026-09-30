-- Prove2me | solution 2 for lean_workbook_plus_52211
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:04:54.339909+00:00
-- url     : https://prove2.me/submissions/086c3220-9196-447b-b20d-d8059ef80840

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h : x * y ≥ 1) :
  1 / (x ^ 2 + 1) + 1 / (y ^ 2 + 1) ≥ 2 / (1 + x * y) := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
