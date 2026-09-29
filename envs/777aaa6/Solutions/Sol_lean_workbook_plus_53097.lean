-- Prove2me | solution 1 for lean_workbook_plus_53097
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:46:57.187434+00:00
-- url     : https://prove2.me/submissions/5e54188a-2e69-49b1-8576-940a881e2906

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : x ≥ y) (hy : y ≥ z) (hz : z ≥ 0) : (x - y) * (y - z) * (x - z) ≥ 0 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
