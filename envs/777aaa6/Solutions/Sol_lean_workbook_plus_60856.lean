-- Prove2me | solution 1 for lean_workbook_plus_60856
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:32:42.476289+00:00
-- url     : https://prove2.me/submissions/3fd3f599-41e8-4f48-88bf-ee247185820d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h : 1 ≤ x * y) :
  1 / (1 + x ^ 2) + 1 / (1 + y ^ 2) ≥ 2 / (1 + x * y) := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
