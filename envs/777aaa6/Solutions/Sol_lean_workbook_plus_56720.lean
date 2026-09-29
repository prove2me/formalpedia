-- Prove2me | solution 1 for lean_workbook_plus_56720
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:23:47.893265+00:00
-- url     : https://prove2.me/submissions/9a41da23-a13d-42a1-bf92-9425bed919cb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : x ≥ 1) (hy : y ≥ 1) : (x + 1) * (y + 1) ≤ 2 * (x * y + 1) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
