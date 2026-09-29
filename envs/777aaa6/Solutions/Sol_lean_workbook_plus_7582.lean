-- Prove2me | solution 1 for lean_workbook_plus_7582
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:58:50.109+00:00
-- url     : https://prove2.me/submissions/c4fb5838-dbe1-4b46-a6f2-ee34f62ed831

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : (x - y) ^ 2 * (4 * x ^ 2 + 7 * x * y + 4 * y ^ 2) ≥ 0 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
