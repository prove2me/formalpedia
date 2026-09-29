-- Prove2me | solution 1 for lean_workbook_plus_60699
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:00:31.454661+00:00
-- url     : https://prove2.me/submissions/7600b80e-0c25-424c-b5e8-b4a308a0c158

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h : 0 < x ∧ 0 < y ∧ 0 < z) (h' : x * y + y * z + z * x = 27) : x + y + z >= 9 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
