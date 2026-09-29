-- Prove2me | solution 1 for lean_workbook_plus_23162
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:54:48.137865+00:00
-- url     : https://prove2.me/submissions/727a4a49-0755-4eb0-b554-c2885e4337f2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : z^2 + x^2 ≥ 2 * x * z := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
