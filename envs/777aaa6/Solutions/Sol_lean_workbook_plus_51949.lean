-- Prove2me | solution 1 for lean_workbook_plus_51949
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:05:26.770486+00:00
-- url     : https://prove2.me/submissions/0d6cf995-cee8-4919-a7c9-4a66e096262b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h : x^2 + y^2 ≤ x + y) : x + y ≤ 2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
