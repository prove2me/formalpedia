-- Prove2me | solution 1 for lean_workbook_plus_32793
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:05:49.893298+00:00
-- url     : https://prove2.me/submissions/606000c3-05bb-42fb-ae98-c115bf28b1cf

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : x^2 + y^2 ≥ 2 * x * y := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
