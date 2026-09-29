-- Prove2me | solution 1 for lean_workbook_plus_12047
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:48:29.49006+00:00
-- url     : https://prove2.me/submissions/f3b14d21-dee0-4ea0-8e06-2d414e75cbac

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) : (x^2 + 1) * (y^2 + 1) ≥ (x * y + 1)^2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
