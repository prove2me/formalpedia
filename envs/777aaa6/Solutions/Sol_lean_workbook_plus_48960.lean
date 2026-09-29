-- Prove2me | solution 1 for lean_workbook_plus_48960
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:37:20.946848+00:00
-- url     : https://prove2.me/submissions/a0ff8538-ff99-4b9f-9517-8ac2f7bc315a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (u v w x y z : ℝ) : -(u - v) * (w + v) - (v - w) * (w + u) - (w - u) * (u + v) + (x + y + z - u - v - w) ^ 2 ≥ 0 := by
  (intros; nlinarith [sq_nonneg (u), sq_nonneg (v), sq_nonneg (w), sq_nonneg (x), sq_nonneg (u - v), sq_nonneg (u - w), sq_nonneg (u - x), sq_nonneg (v - w), sq_nonneg (v - x), sq_nonneg (w - x), sq_nonneg (u + v), sq_nonneg (u + w), sq_nonneg (u + x), sq_nonneg (v + w), sq_nonneg (v + x), sq_nonneg (w + x)])
