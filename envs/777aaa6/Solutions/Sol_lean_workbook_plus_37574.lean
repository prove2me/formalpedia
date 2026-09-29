-- Prove2me | solution 1 for lean_workbook_plus_37574
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:53:28.622075+00:00
-- url     : https://prove2.me/submissions/f1fe7010-32bb-4561-b0a6-18f0c6daa12d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : (x + y) ^ 2 + (y + z) ^ 2 + (z + x) ^ 2 ≥ (4 * (x + y + z) ^ 2)/3 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
