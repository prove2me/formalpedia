-- Prove2me | solution 1 for lean_workbook_plus_67866
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:13:28.847307+00:00
-- url     : https://prove2.me/submissions/5783ff61-82a1-4553-a8fb-ba7517158657

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h : x*y = 1) : 4 + x^2 + y^2 ≥ 3 * (x + y) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
