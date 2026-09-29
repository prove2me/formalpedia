-- Prove2me | solution 1 for lean_workbook_plus_49192
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:36:56.632898+00:00
-- url     : https://prove2.me/submissions/831c9868-d296-4275-9830-671f4d71425a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx: x ≥ 0) (hy: y^2 ≥ x * (x + 1)) : (y - 1)^2 ≥ x * (x - 1) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
