-- Prove2me | solution 1 for lean_workbook_plus_45426
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:38:25.906268+00:00
-- url     : https://prove2.me/submissions/b3d38cd4-e577-4465-9a05-3b10715c4e57

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h : x + y + z = 3) : x*y + x*z + y*z ≤ 3 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
